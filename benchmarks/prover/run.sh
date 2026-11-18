#!/usr/bin/env bash
set -Eeuo pipefail
PROVER_HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=../suite/common.sh
source "$PROVER_HERE/../suite/common.sh"
PROVER_BUILD=$BENCH_BUILD/prover
PROVER_RESULTS=$BENCH_RESULTS/prover

usage() {
    cat <<'HELP'
Usage: bash benchmarks/prover/run.sh plan|build|run|report [options]
  --preset quick|full  --target native|avx2|avx2-gfni|avx512
  --revisions previous,current  --provers stable,experimental
  --threads 1,16  --workloads sphincs-16,xmss-128,recursion-sphincs-2x16
  --repeat N  --log-inverse-rate N  --timeout SECONDS
  --session PATH [--resume]  --measurements FILE
  --execute     Required with run, including fixture preparation
The CLI is unmodified. Both provers are compiled in and selected at runtime.
plan/build never generate signatures or proofs. Default workers adapt to available cores.
HELP
}

prover_plan() {
    local capabilities=$1 cpus
    cpus=$(physical_cpu_ids | jq -Rsc 'split("\n")[:-1]|map(tonumber)')
    jq --arg preset "$preset" --arg target "$target" --arg revisions "$revisions" --arg provers "$provers" \
        --arg workloads "$workloads" --arg threads "$threads" --arg repeat "$repeat" --arg rate "$rate" \
        --argjson cpus "$cpus" --argjson capabilities "$capabilities" -f "$PROVER_HERE/plan.jq" "$PROVER_HERE/config.json"
}

prover_checkout() {
    local sha=$1 directory cargo_root=${CARGO_HOME:-$HOME/.cargo}
    while IFS= read -r -d '' directory; do
        if [[ $(git -C "$directory" rev-parse HEAD 2>/dev/null) == "$sha" ]]; then printf '%s\n' "$directory"; return; fi
    done < <(find "$cargo_root/git/checkouts" -mindepth 2 -maxdepth 2 -type d -name "${sha:0:7}*" -print0)
    fail "Cannot find Cargo's checkout for $sha"
}

build_provers() {
    local plan=$1 revision sha destination encoded checkout binary compiler metadata model cpu_signature
    local -a flags command
    mapfile -t flags < <(jq -r '.rustflags[]' <<<"$plan")
    encoded=$(IFS=$'\x1f'; printf '%s' "${flags[*]}")
    compiler=$(rustc "+$(jq -r .toolchain "$PROVER_HERE/config.json")" -vV)
    model=$(machine_snapshot "$(jq '.jobs[0].cpus[0]' <<<"$plan")" | jq -r .model_name)
    cpu_signature=$(printf '%s:%s' "$model" "$(jq -cS .capabilities <<<"$plan")" | sha256sum | cut -c1-16)
    while IFS=$'\t' read -r revision sha; do
        destination=$PROVER_BUILD/$revision-$(jq -r .target <<<"$plan")
        mkdir -p -- "$destination"
        local build_lock; exec {build_lock}>"$destination/build.lock"
        flock -n "$build_lock" || { fail 'Another prover build owns this target'; return 1; }
        command=(env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS "CARGO_ENCODED_RUSTFLAGS=$encoded" \
            "CARGO_TARGET_DIR=$BENCH_BUILD/cargo/prover/$revision-${sha:0:12}-$(jq -r .target <<<"$plan")-$cpu_signature" \
            CARGO_BUILD_JOBS=8 CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 CARGO_PROFILE_RELEASE_OPT_LEVEL=3 \
            cargo "+$(jq -r .toolchain "$PROVER_HERE/config.json")" install leanvm-cli \
            --git "$(jq -r .repository "$PROVER_HERE/config.json")" --rev "$sha" --locked --bin leanvm --root "$destination" --force)
        printf 'Building unmodified leanVM %s at %s\n' "$revision" "$sha" >&2
        "${command[@]}" >"$destination/build.log" 2>&1 || { fail "Prover build failed; inspect $destination/build.log"; return 1; }
        binary=$destination/bin/leanvm
        "$binary" --help >"$destination/help.txt"
        grep -F -- '--prover' "$destination/help.txt" >/dev/null && grep -F stable "$destination/help.txt" >/dev/null && \
            grep -F experimental "$destination/help.txt" >/dev/null || { fail 'Unexpected stock CLI options'; return 1; }
        checkout=$(prover_checkout "$sha")
        git -C "$checkout" diff --exit-code HEAD -- >/dev/null || { fail 'Upstream source has local modifications'; return 1; }
        atomic_json "$destination/build.json" -n --arg sha "$sha" --arg hash "$(digest "$binary")" --arg compiler "$compiler" \
            --arg model "$model" --argjson capabilities "$(jq -c .capabilities <<<"$plan")" \
            --arg lock "$(digest "$checkout/Cargo.lock")" --arg cache "$checkout/target/signers-cache" \
            --argjson flags "$(json_array "${flags[@]}")" --argjson command "$(json_command "${command[@]}")" \
            '{sha:$sha,binary_sha256:$hash,rustc:$compiler,rustflags:$flags,build_cpu_model:$model,capabilities:$capabilities,cargo_lock_sha256:$lock,
              cache_directory:$cache,command:$command,cargo_features:"Upstream default CLI dependencies, aggregation/signers-cache; both provers compiled in"}'
        exec {build_lock}>&-
    done < <(jq -r '.jobs|unique_by(.revision)|.[]|[.revision,.sha]|@tsv' <<<"$plan")
}

fixture_counts() {
    jq -c '[.jobs[].arguments|.[0] as $kind | (.[1:]|[range(0;length;2) as $i|{key:.[$i],value:(.[$i+1]|tonumber)}]|from_entries) as $a |
      {sphincs:(if $kind=="recursion" then ($a["--n"]//2)*($a["--sphincs-per-leaf"]//0) else $a["--sphincs"]//0 end),
       xmss:(if $kind=="recursion" then ($a["--n"]//2)*($a["--xmss-per-leaf"]//900) else $a["--xmss"]//0 end)}] |
       {sphincs:(map(.sphincs)|max),xmss:(map(.xmss)|max)}'
}

prover_invocation() {
    local job=$1 plan=$2 directory=$3 repeats=$4 cooldown_seconds=$5 stem=$3/cli binary cpus metrics
    local -a arguments command
    [[ ! -e $directory ]] || { fail 'CLI output directory already exists'; return 1; }
    mkdir -p -- "$directory"
    binary=$PROVER_BUILD/$(jq -r .revision <<<"$job")-$(jq -r .target <<<"$plan")/bin/leanvm
    cpus=$(jq -r '.cpus|join(",")' <<<"$job")
    mapfile -t arguments < <(jq -r '.arguments[]' <<<"$job")
    command=("$binary" --prover "$(jq -r .prover <<<"$job")" --repeat "$repeats" --cooldown "$cooldown_seconds" \
        --log-inv-rate "$(jq -r .log_inverse_rate <<<"$plan")" "${arguments[@]}")
    (cd -- "$directory"; run_logged "$stem" "$cpus" "$timeout_seconds" env -u RUST_LOG "LEANVM_NUM_THREADS=$(jq -r .threads <<<"$job")" "${command[@]}")
    metrics=$(jq -n --rawfile stdout "$stem.stdout.log" --rawfile stderr "$stem.stderr.log" '{stdout:$stdout,stderr:$stderr}' |
        jq --argjson repeat "$repeats" -f "$PROVER_HERE/parse.jq")
    atomic_json "$directory/execution.json" -n --argjson job "$job" --argjson command "$(json_command "${command[@]}")" \
        --arg hash "$(digest "$binary")" --argjson metrics "$metrics" \
        '{job:$job,command:$command,binary_sha256:$hash,returncode:0,metrics:$metrics}'
}

cache_hashes() {
    local directory=$1 counts=$2 scheme file hashes='{}'; local -a files
    for scheme in sphincs xmss; do
        [[ $(jq -r --arg scheme "$scheme" '.[$scheme]' <<<"$counts") != 0 ]] || continue
        shopt -s nullglob; files=("$directory/lean_${scheme}_signers_"*.bin)
        ((${#files[@]}==1)) || { fail "Missing or ambiguous $scheme signer cache"; return 1; }
        file=${files[0]}
        hashes=$(jq -c --arg name "$(basename -- "$file")" --arg hash "$(digest "$file")" '.+{($name):$hash}' <<<"$hashes")
    done
    jq -cS . <<<"$hashes"
}

run_provers() {
    local plan=$1 directory state machine snapshot metadata revision sha job destination compiler common_cache= cache counts cpus id key stem record ordered
    [[ $execute == true ]] || { fail 'Measurements require run --execute'; return 1; }
    directory=$(realpath -m -- "${session:-$PROVER_RESULTS/$(date -u +%Y%m%dT%H%M%SZ)}")
    [[ ! -e $directory || $resume == true ]] || { fail 'Session exists; choose another path or --resume'; return 1; }
    mkdir -p -- "$directory"; state=$directory/session.json
    machine=$(machine_snapshot "$(jq '.jobs[0].cpus[0]' <<<"$plan")")
    snapshot=$(source_snapshot); counts=$(fixture_counts <<<"$plan")
    compiler=$(rustc "+$(jq -r .toolchain "$PROVER_HERE/config.json")" -vV)
    if [[ $resume == true ]]; then
        jq -e --argjson plan "$plan" --arg hash "$(jq -r .source_sha256 <<<"$snapshot")" '.plan==$plan and .source.source_sha256==$hash' "$state" >/dev/null || { fail 'Resume plan or source differs'; return 1; }
        require_same_machine "$(jq -c .machine "$state")" "$machine"
    else
        atomic_json "$state" -n --argjson plan "$plan" --argjson source "$snapshot" --argjson machine "$machine" \
            '{schema_version:2,plan:$plan,source:$source,machine:$machine,completed:{},builds:{},fixture_cache_sha256:{},complete:false}'
    fi
    while IFS=$'\t' read -r revision sha; do
        destination=$PROVER_BUILD/$revision-$(jq -r .target <<<"$plan")
        [[ -f $destination/build.json ]] || { fail "Build the $revision prover first"; return 1; }
        metadata=$(<"$destination/build.json")
        jq -e --arg sha "$sha" --argjson flags "$(jq -c .rustflags <<<"$plan")" --arg compiler "$compiler" \
            --arg model "$(jq -r .model_name <<<"$machine")" --argjson capabilities "$(jq -c .capabilities <<<"$plan")" \
            '.sha==$sha and .rustflags==$flags and .rustc==$compiler and .build_cpu_model==$model and .capabilities==$capabilities' <<<"$metadata" >/dev/null || { fail 'Prover source, CPU flags or compiler changed'; return 1; }
        [[ $(digest "$destination/bin/leanvm") == "$(jq -r .binary_sha256 <<<"$metadata")" ]] || { fail 'Prover binary changed'; return 1; }
        if jq -e --arg revision "$revision" '.builds|has($revision)' "$state" >/dev/null; then
            [[ $(jq -r --arg revision "$revision" '.builds[$revision].binary_sha256' "$state") == "$(jq -r .binary_sha256 <<<"$metadata")" ]] || { fail 'Session prover binary changed'; return 1; }
        fi
        atomic_json "$state" --arg revision "$revision" --argjson metadata "$metadata" '.builds[$revision]=$metadata' "$state"
        cache=$(jq -r .cache_directory <<<"$metadata")
        if [[ $resume != true ]] || ! jq -e --arg revision "$revision" '.fixture_cache_sha256|has($revision)' "$state" >/dev/null; then
            job=$(jq -c --arg revision "$revision" '[.jobs[]|select(.revision==$revision)]|max_by(.threads)' <<<"$plan")
            local scheme count prep
            for scheme in sphincs xmss; do
                count=$(jq -r --arg scheme "$scheme" '.[$scheme]' <<<"$counts")
                ((count>0)) || continue
                prep=$(jq --arg scheme "$scheme" --arg count "$count" '.arguments=["aggregate",("--"+$scheme),$count]' <<<"$job")
                local preparation=$directory/prepare-$revision-$scheme
                if [[ -e $preparation ]]; then
                    [[ $(dirname -- "$(realpath -- "$preparation")") == "$directory" ]] || { fail 'Unsafe cache preparation path'; return 1; }
                    mkdir -p -- "$directory/attempts"
                    mv -- "$preparation" "$directory/attempts/prepare-$revision-$scheme-$(date +%s%N)"
                fi
                prover_invocation "$prep" "$plan" "$preparation" 1 0
            done
        fi
        metadata=$(cache_hashes "$cache" "$counts")
        [[ -z $common_cache || $metadata == "$common_cache" ]] || { fail 'Signer caches differ across revisions; stop before timing'; return 1; }
        if [[ $resume == true ]] && jq -e --arg revision "$revision" '.fixture_cache_sha256|has($revision)' "$state" >/dev/null; then
            [[ $metadata == "$(jq -cS --arg revision "$revision" '.fixture_cache_sha256[$revision]' "$state")" ]] || { fail 'Cached inputs changed since session start'; return 1; }
        fi
        common_cache=$metadata
        atomic_json "$state" --arg revision "$revision" --argjson hashes "$metadata" '.fixture_cache_sha256[$revision]=$hashes' "$state"
    done < <(jq -r '.jobs|unique_by(.revision)|.[]|[.revision,.sha]|@tsv' <<<"$plan")
    ordered=$(jq -c '.jobs[]' <<<"$plan" | while IFS= read -r job; do
        printf '%s\t%s\n' "$(printf '%s:%s' "$(jq -r .shuffle_seed <<<"$plan")" "$job" | sha256sum | cut -d ' ' -f1)" "$job"
    done | sort | cut -f2-)
    while IFS= read -r job; do
        id=$(jq -r '[.revision,.prover,(.threads|tostring)+"t",.workload]|join("-")' <<<"$job")
        stem=$directory/$id
        if jq -e --arg id "$id" '.completed|has($id)' "$state" >/dev/null; then
            key=$(jq -r --arg id "$id" '.completed[$id].sha256' "$state")
            [[ -f $stem/execution.json && $(digest "$stem/execution.json") == "$key" ]] || { fail 'Completed prover data changed'; return 1; }
            [[ $(digest "$stem/cli.stdout.log") == "$(jq -r --arg id "$id" '.completed[$id].stdout_sha256' "$state")" && \
               $(digest "$stem/cli.stderr.log") == "$(jq -r --arg id "$id" '.completed[$id].stderr_sha256' "$state")" ]] || { fail 'Completed prover logs changed'; return 1; }
            continue
        fi
        if [[ -e $stem ]]; then
            local archive=$directory/attempts/$id-$(date +%s%N)
            mkdir -p -- "$(dirname -- "$archive")"
            [[ $(dirname -- "$(realpath -- "$stem")") == "$directory" ]] || { fail 'Unsafe interrupted job path'; return 1; }
            mv -- "$stem" "$archive"
        fi
        require_same_machine "$machine" "$(machine_snapshot "$(jq '.jobs[0].cpus[0]' <<<"$plan")")"
        printf 'Running %s\n' "$id" >&2
        prover_invocation "$job" "$plan" "$stem" "$(jq -r .repeat <<<"$plan")" "$(jq -r .cooldown_seconds <<<"$plan")"
        require_same_machine "$machine" "$(machine_snapshot "$(jq '.jobs[0].cpus[0]' <<<"$plan")")"
        revision=$(jq -r .revision <<<"$job")
        cache=$(jq -r --arg revision "$revision" '.builds[$revision].cache_directory' "$state")
        [[ $(cache_hashes "$cache" "$counts") == "$common_cache" ]] || { fail 'Signer cache changed during a measured job'; return 1; }
        atomic_json "$state" --arg id "$id" --arg file "$id/execution.json" --arg hash "$(digest "$stem/execution.json")" \
            --arg out "$(digest "$stem/cli.stdout.log")" --arg err "$(digest "$stem/cli.stderr.log")" \
            '.completed[$id]={file:$file,sha256:$hash,stdout_sha256:$out,stderr_sha256:$err}' "$state"
    done <<<"$ordered"
    atomic_json "$state" '.complete=true' "$state"
    printf 'Complete: %s\n' "$directory"
}

main() {
    local action=${1:-help}; (($#==0)) || shift
    preset=quick; target=native; revisions=; provers=; threads=; workloads=; repeat=; rate=; timeout_seconds=900
    execute=false; session=; resume=false; measurements=
    while (($#)); do
        case "$1" in
            --preset|--target|--revisions|--provers|--threads|--workloads|--repeat|--log-inverse-rate|--timeout|--session|--measurements)
                (($#>=2)) || { fail "Missing value: $1"; return 1; }
                case "$1" in --log-inverse-rate) rate=$2;; --timeout) timeout_seconds=$2;; *) printf -v "${1#--}" '%s' "$2";; esac; shift 2;;
            --execute) execute=true;shift;; --resume) resume=true;shift;; --help|-h) usage;return;;
            *) fail "Unknown option: $1";return 1;;
        esac
    done
    case "$action" in help|--help|-h) usage;return;; plan|build|run|report) ;; *) fail "Unknown action: $action";return 1;; esac
    [[ $action != run || $execute == true ]] || { fail 'Measurements require run --execute';return 1; }
    linux_requirements
    if [[ $action == report ]]; then source "$PROVER_HERE/report.sh"; report_provers "$session" "$measurements"; return; fi
    [[ -z $measurements ]] || { fail '--measurements is report-only';return 1; }
    integer "$timeout_seconds" && ((timeout_seconds>0)) || { fail 'Timeout must be a positive integer'; return 1; }
    [[ -z $repeat ]] || integer "$repeat" || { fail 'Repeat must be an integer';return 1; }
    [[ -z $rate ]] || integer "$rate" || { fail 'Inverse rate must be an integer';return 1; }
    need cargo rustc
    local capabilities plan
    capabilities=$(cpu_capabilities "$(jq -r .toolchain "$PROVER_HERE/config.json")")
    plan=$(prover_plan "$capabilities")
    case "$action" in
        plan) jq . <<<"$plan";; build) build_provers "$plan";;
        run) lock_cpus "$(jq -r '[.jobs[].cpus[]]|unique|join(",")' <<<"$plan")"; run_provers "$plan";;
    esac
}
if [[ ${BASH_SOURCE[0]} == "$0" ]]; then main "$@"; fi
