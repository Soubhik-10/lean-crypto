#!/usr/bin/env bash
set -Eeuo pipefail
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=suite/common.sh
source "$HERE/suite/common.sh"

usage() {
    cat <<'HELP'
Usage: bash benchmarks/run.sh plan|build|run|report [options]
  --profile raw|rust|quick|comparison|publication|comprehensive|hashes
  --targets baseline,v2,v3,v4,native  --hashing portable,tiny,assembly
  --recovery libsecp256k1,k256       --groups direct,ecrecover,macro,reject,hash,batched
  --samples N  --sample-ms N  --passes N  --cpu N  --cooldown-seconds N
  --disable-slp  --unmodified-tiny  --per-fixture
  --session PATH [--resume]          Run a new session or resume verified tasks
  --measurements FILE               Report published JSON; runs no binary
  --bootstrap N                     Block-bootstrap resamples (default 2000)
  --timeout SECONDS                 Per-binary limit; 0 means no limit
  --no-reference                    Omit comparison columns in generated reports
Requires Linux, Bash 4.3+, jq 1.6+, awk, Rust, coreutils and util-linux.
Only the run action measures. plan and build never generate signatures or proofs.
HELP
}

native_plan() {
    local capabilities=$1
    jq --arg profile "$profile" --arg targets "$targets" --arg hashing "$hashing" --arg recovery "$recovery" \
        --arg groups "$groups" --arg samples "$samples" --arg sample_ms "$sample_ms" --arg passes "$passes" \
        --arg cooldown "$cooldown" --argjson cpu "$cpu" --argjson capabilities "$capabilities" \
        --argjson per_fixture "$per_fixture" --argjson disable_slp "$disable_slp" --argjson unmodified_tiny "$unmodified_tiny" \
        -f "$HERE/suite/plan.jq" "$HERE/suite/config.json"
}

build_native() {
    local plan=$1 start compiler index job id target features flags encoded metadata graph binary description entry ending
    local -a feature_args flags_array command
    local cc_program=${CC:-cc} cc_path= cc_version="Compiler version unavailable"
    if cc_path=$(command -v -- "$cc_program"); then
        cc_version=$("$cc_program" --version 2>&1) || cc_version="Compiler version unavailable"
    fi
    mkdir -p -- "$BENCH_BUILD"
    local build_lock; exec {build_lock}>"$BENCH_BUILD/build.lock"
    flock -n "$build_lock" || { fail 'Another build is updating this build directory'; return 1; }
    start=$(source_snapshot); compiler=$(rustc "+$(jq -r .toolchain <<<"$plan")" -vV)
    index=$(jq -n --argjson source "$start" --arg compiler "$compiler" --arg cargo "$(cargo -V)" \
        '{schema_version:2,source:$source,rustc:$compiler,cargo:$cargo,jobs:{}}')
    if [[ -f $BENCH_BUILD/builds.json ]] && jq -e --arg hash "$(jq -r .source_sha256 <<<"$start")" --arg compiler "$compiler" \
        '.source.source_sha256==$hash and .rustc==$compiler' "$BENCH_BUILD/builds.json" >/dev/null; then
        index=$(<"$BENCH_BUILD/builds.json")
    fi
    while IFS= read -r job; do
        id=$(jq -r .id <<<"$job"); target=$(jq -r .target.id <<<"$job")
        feature_args=(); features=$(jq -r '.features|join(",")' <<<"$job")
        [[ -z $features ]] || feature_args=(--features "$features")
        mapfile -t flags_array < <(jq -r '["-C",("target-cpu="+.target.cpu)]+.extra_rustflags|.[]' <<<"$job")
        encoded=$(IFS=$'\x1f'; printf '%s' "${flags_array[*]}")
        command=(env -u RUSTFLAGS -u SHA3_ASM_SCRIPT "CARGO_ENCODED_RUSTFLAGS=$encoded" \
            "CARGO_TARGET_DIR=$BENCH_BUILD/cargo/$target" CARGO_PROFILE_BENCH_LTO=thin \
            CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 CARGO_PROFILE_BENCH_OPT_LEVEL=3 CARGO_PROFILE_BENCH_INCREMENTAL=false)
        metadata=$("${command[@]}" cargo "+$(jq -r .toolchain <<<"$plan")" metadata --format-version 1 \
            --manifest-path "$HERE/evm2/Cargo.toml" --locked --no-default-features "${feature_args[@]}")
        graph=$(jq -c '(.resolve.nodes|map({key:.id,value:.features})|from_entries) as $nodes |
            [.packages[]|{name,version,source,features:($nodes[.id]//[])}]' <<<"$metadata")
        jq -e 'all(.[]; .name!="alloy-primitives" or (.features|index("keccak-cache-global")|not))' <<<"$graph" >/dev/null || \
            { fail 'Global Keccak caching must be disabled'; return 1; }
        command+=(cargo "+$(jq -r .toolchain <<<"$plan")" build --profile bench --bench matrix --manifest-path "$HERE/evm2/Cargo.toml" \
            --locked --no-default-features --message-format=json-render-diagnostics "${feature_args[@]}")
        printf 'Building %s\n' "$id" >&2
        "${command[@]}" >"$BENCH_BUILD/$id.build.stdout.log" 2>"$BENCH_BUILD/$id.build.stderr.log" || \
            { fail "Build failed; inspect $BENCH_BUILD/$id.build.stderr.log"; return 1; }
        binary=$(jq -ser '[.[]|select(.reason=="compiler-artifact" and .target.name=="matrix" and .executable!=null)|.executable] |
            if length==1 then .[0] else error("Expected exactly one matrix binary") end' "$BENCH_BUILD/$id.build.stdout.log")
        install -m 755 -- "$binary" "$BENCH_BUILD/$id"
        binary=$BENCH_BUILD/$id; description=$("$binary" --describe)
        jq -e --argjson job "$job" '.build.keccak_backend==$job.keccak and .build.ecrecover==$job.ecrecover and
            (($job.groups|index("direct")|not) or (.build.experimental_adapter==false))' <<<"$description" >/dev/null || \
            { fail 'Compiled backend, provider or adapter marker disagrees with the plan'; return 1; }
        entry=$(jq -n --argjson configuration "$job" --arg binary "$binary" --arg hash "$(digest "$binary")" \
            --argjson build "$description" --argjson graph "$graph" --argjson flags "$(json_array "${flags_array[@]}")" \
            --argjson command "$(json_command "${command[@]}")" --arg cc "${CC-}" --arg cflags "${CFLAGS-}" \
            --arg cxx "${CXX-}" --arg cxxflags "${CXXFLAGS-}" \
            --arg cc_path "$cc_path" --arg cc_version "$cc_version" \
            '{configuration:$configuration,binary:$binary,binary_sha256:$hash,build:$build,command:$command,
              resolved_cargo_features:$graph,rustflags:$flags,
              profile:{optimization:3,lto:"thin",codegen_units:1,incremental:false},
              cflags:{CC:$cc,CFLAGS:$cflags,CC_PATH:$cc_path,CC_VERSION:$cc_version,CXX:$cxx,CXXFLAGS:$cxxflags}}')
        index=$(jq --arg id "$id" --argjson entry "$entry" '.jobs[$id]=$entry' <<<"$index")
        atomic_json "$BENCH_BUILD/builds.json" '.' <<<"$index"
    done < <(jq -c '.jobs[]' <<<"$plan")
    ending=$(source_snapshot)
    [[ $(jq -r .source_sha256 <<<"$start") == "$(jq -r .source_sha256 <<<"$ending")" ]] || { fail 'Sources changed during build'; return 1; }
}

load_native_builds() {
    local plan=$1 snapshot compiler job id binary
    [[ -f $BENCH_BUILD/builds.json ]] || { fail 'Build the selected configurations first'; return 1; }
    snapshot=$(source_snapshot); compiler=$(rustc "+$(jq -r .toolchain <<<"$plan")" -vV)
    jq -e --arg hash "$(jq -r .source_sha256 <<<"$snapshot")" --arg compiler "$compiler" \
        '.source.source_sha256==$hash and .rustc==$compiler' "$BENCH_BUILD/builds.json" >/dev/null || \
        { fail 'Source or compiler changed; rebuild before measuring'; return 1; }
    while IFS= read -r job; do
        id=$(jq -r .id <<<"$job")
        jq -e --arg id "$id" --argjson job "$job" '.jobs[$id].configuration==$job' "$BENCH_BUILD/builds.json" >/dev/null || \
            { fail "Missing or mismatched build: $id"; return 1; }
        binary=$(jq -r --arg id "$id" '.jobs[$id].binary' "$BENCH_BUILD/builds.json")
        [[ -f $binary ]] && [[ $(digest "$binary") == "$(jq -r --arg id "$id" '.jobs[$id].binary_sha256' "$BENCH_BUILD/builds.json")" ]] || \
            { fail "Binary hash changed: $id"; return 1; }
    done < <(jq -c '.jobs[]' <<<"$plan")
}

run_native() {
    local plan=$1 directory state snapshot source builds job id task path pass corpus_hash report_hash binary jobs before after actual expected
    local -a command
    load_native_builds "$plan"
    directory=${session:-$BENCH_RESULTS/$(date -u +%Y%m%dT%H%M%SZ)}
    directory=$(realpath -m -- "$directory")
    if [[ -e $directory && $resume != true ]]; then fail 'Session already exists; choose another path or --resume'; return 1; fi
    mkdir -p -- "$directory"
    state=$directory/session.json; snapshot=$(machine_snapshot "$cpu"); source=$(source_snapshot)
    builds=$(<"$BENCH_BUILD/builds.json")
    if [[ $resume == true ]]; then
        [[ -f $state ]] || { fail 'No session journal to resume'; return 1; }
        jq -e --argjson plan "$plan" --arg hash "$(jq -r .source_sha256 <<<"$source")" \
            '.plan==$plan and .source.source_sha256==$hash' "$state" >/dev/null || { fail 'Resume plan or source differs'; return 1; }
        require_same_machine "$(jq -c .machine "$state")" "$snapshot"
        jq -e --argjson builds "$builds" '.builds.jobs as $old|all(.plan.jobs[]; .id as $id|$old[$id].binary_sha256==$builds.jobs[$id].binary_sha256)' \
            "$state" >/dev/null || { fail 'A session binary changed'; return 1; }
    else
        atomic_json "$state" -n --arg started "$(utc)" --argjson plan "$plan" --argjson source "$source" \
            --argjson builds "$builds" --argjson machine "$snapshot" \
            '{schema_version:2,started_utc:$started,plan:$plan,source:$source,builds:$builds,machine:$machine,completed:{},segments:[]}'
    fi
    atomic_json "$state" --arg started "$(utc)" --argjson machine "$snapshot" '.segments += [{started_utc:$started,machine:$machine}]' "$state"
    for ((pass=1;pass<=$(jq -r .profile.passes <<<"$plan");pass++)); do
        # Hash-based deterministic permutation avoids a platform-dependent shuffle.
        jobs=$(jq -r --arg pass "$pass" '.jobs[].id+"\t"+$pass' <<<"$plan" | while IFS=$'\t' read -r id ordinal; do
            printf '%s\t%s\n' "$(printf '%s:%s:%s' "$(jq -r .seed <<<"$plan")" "$ordinal" "$id" | sha256sum | cut -d ' ' -f 1)" "$id"
        done | sort | cut -f2)
        while IFS= read -r id; do
            job=$(jq -c --arg id "$id" '.jobs[]|select(.id==$id)' <<<"$plan")
            printf -v task 'pass-%02d-%s' "$pass" "$id"; path=$directory/$task.json
            if jq -e --arg task "$task" '.completed|has($task)' "$state" >/dev/null; then
                [[ -f $path ]] && [[ $(digest "$path") == "$(jq -r --arg task "$task" '.completed[$task].sha256' "$state")" ]] || { fail 'Completed raw data changed'; return 1; }
                validate_native_report "$path" "$(jq -r .profile.samples <<<"$plan")"
                [[ -f $directory/corpus.json ]] && [[ $(digest "$directory/corpus.json") == "$(jq -r .corpus_sha256 "$state")" ]] || { fail 'Shared corpus changed'; return 1; }
                continue
            fi
            archive_attempt "$directory" "$task"
            binary=$(jq -r --arg id "$id" '.jobs[$id].binary' <<<"$builds")
            command=("$binary" --run --samples "$(jq -r .profile.samples <<<"$plan")" --sample-ms "$(jq -r .profile.sample_ms <<<"$plan")" \
                --warmup-ms "$(jq -r .profile.warmup_ms <<<"$plan")" --seed "$(( $(jq -r .seed <<<"$plan") + pass - 1 ))" \
                --extra-cases "$(jq -r .profile.extra_cases <<<"$plan")" --groups "$(jq -r '.groups|join(",")' <<<"$job")" \
                --json "$path" --corpus-json "$directory/corpus.json" --wait-for-start)
            [[ $(jq -r .profile.per_fixture <<<"$plan") != true ]] || command+=(--per-fixture)
            before=$(machine_snapshot "$cpu"); require_same_machine "$snapshot" "$before"
            printf 'Starting %s\n' "$task" >&2
            run_logged "$directory/$task" "$cpu" "$timeout_seconds" "${command[@]}"
            after=$(machine_snapshot "$cpu"); require_same_machine "$before" "$after"
            validate_native_report "$path" "$(jq -r .profile.samples <<<"$plan")"
            actual=$(jq -cS .build "$path"); expected=$(jq -cS --arg id "$id" '.jobs[$id].build.build' <<<"$builds")
            [[ $actual == "$expected" ]] || { fail 'Report build marker differs from measured binary'; return 1; }
            [[ $(jq '.measurements|length' "$path") == "$(jq .case_count <<<"$job")" ]] || { fail 'Unexpected case count'; return 1; }
            corpus_hash=$(digest "$directory/corpus.json"); report_hash=$(digest "$path")
            jq -e --arg hash "$corpus_hash" '.corpus_sha256==null or .corpus_sha256==$hash' "$state" >/dev/null || { fail 'Shared corpus changed'; return 1; }
            atomic_json "$state" --arg corpus "$corpus_hash" --arg task "$task" --arg id "$id" --arg file "$task.json" \
                --arg hash "$report_hash" --argjson pass "$pass" --argjson machine "$before" \
                '.corpus_sha256=$corpus | .completed[$task]={configuration:$id,pass:$pass,file:$file,sha256:$hash,machine_before:$machine}' "$state"
            sleep "$(jq -r .cooldown_seconds <<<"$plan")"
        done <<<"$jobs"
    done
    atomic_json "$state" --arg finished "$(utc)" '.finished_utc=$finished' "$state"
    printf 'Completed session: %s\n' "$directory"
}

main() {
    local action=${1:-help}; (($#==0)) || shift
    profile=raw; targets=; hashing=; recovery=; groups=; samples=; sample_ms=; passes=; cooldown=; cpu=
    disable_slp=false; unmodified_tiny=false; per_fixture=false; session=; resume=false; measurements=; bootstrap=2000
    timeout_seconds=0; include_reference=true
    while (($#)); do
        case "$1" in
            --profile|--targets|--hashing|--recovery|--groups|--samples|--sample-ms|--passes|--cooldown-seconds|--cpu|--session|--measurements|--bootstrap|--timeout)
                (($#>=2)) || { fail "Missing value: $1"; return 1; }
                case "$1" in
                    --sample-ms) sample_ms=$2;; --cooldown-seconds) cooldown=$2;; --timeout) timeout_seconds=$2;;
                    *) local key=${1#--}; key=${key//-/_}; printf -v "$key" '%s' "$2";;
                esac; shift 2;;
            --disable-slp) disable_slp=true; shift;; --unmodified-tiny) unmodified_tiny=true; shift;;
            --per-fixture) per_fixture=true; shift;; --resume) resume=true; shift;;
            --no-reference) include_reference=false; shift;; --include-reference) include_reference=true; shift;;
            --help|-h) usage; return;; *) fail "Unknown option: $1"; return 1;;
        esac
    done
    case "$action" in help|--help|-h) usage; return;; plan|build|run|report) ;; *) fail "Unknown action: $action"; return 1;; esac
    linux_requirements
    local value; for value in "$samples" "$sample_ms" "$passes" "$cooldown"; do [[ -z $value ]] || integer "$value" || { fail 'Expected a nonnegative integer'; return 1; }; done
    integer "$timeout_seconds" && integer "$bootstrap" && ((bootstrap>=100 && bootstrap<=100000)) || { fail 'Invalid timeout or bootstrap count'; return 1; }
    if [[ $action == report ]]; then
        # shellcheck source=suite/report.sh
        source "$HERE/suite/report.sh"
        report_native "$session" "$measurements" "$bootstrap" "$include_reference"
        return
    fi
    [[ -z $measurements ]] || { fail '--measurements is report-only'; return 1; }
    if [[ -z $cpu ]]; then local -a available; mapfile -t available < <(allowed_cpu_ids); cpu=${available[0]}; fi
    check_cpu "$cpu"
    need cargo rustc
    local capabilities plan
    capabilities=$(cpu_capabilities "$(jq -r .toolchain "$HERE/suite/config.json")")
    plan=$(native_plan "$capabilities")
    case "$action" in plan) jq . <<<"$plan";; build) build_native "$plan";; run) lock_cpus "$cpu"; run_native "$plan";; esac
}
if [[ ${BASH_SOURCE[0]} == "$0" ]]; then main "$@"; fi
