#!/usr/bin/env bash
# Matched aggregate verification, using the same metadata/CPU helpers as the signature suite.
set -Eeuo pipefail
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
source "$HERE/suite/common.sh"
usage() {
    cat <<'HELP'
Usage: bash benchmarks/compare.sh verifier [plan|build|run|report] [options]
  --session PATH          Fresh output directory (required for report)
  --cpu N                 Allowed logical CPU (default: first allowed)
  --hashing portable,assembly  Hashing builds (default: both)
  --target-cpu NAME       Rust target CPU (default: native)
  --passes N             Fresh processes per build (default: 3)
  --rounds N             Paired sampling rounds per process (default: 5)
  --iterations N         Verifications per round (default: 30)
  --timeout SECONDS      Per-process limit including proof setup (default: 900)
Only run generates proofs or measures. Program preparation and proving are untimed.
HELP
}
[[ ${1-} != --help && ${1-} != -h ]] || { usage; exit 0; }
action=${1:-run}; (($#==0)) || shift
session=; cpu=; hashing=portable,assembly; target_cpu=native
passes=3; rounds=5; iterations=30; limit=900
toolchain=$(jq -r .toolchain "$HERE/suite/config.json")
while (($#)); do
    case $1 in --help|-h) usage; exit 0;; esac
    (($#>=2)) || { usage >&2; exit 2; }
    case $1 in
        --session) session=$2;; --cpu) cpu=$2;; --hashing) hashing=$2;;
        --target-cpu) target_cpu=$2;; --passes) passes=$2;; --rounds) rounds=$2;;
        --iterations) iterations=$2;; --timeout) limit=$2;;
        *) fail "Unknown verifier option: $1"; exit 2;;
    esac
    shift 2
done
case $action in plan|build|run|report) ;; *) fail "Unknown action: $action"; exit 2;; esac
linux_requirements
need cargo rustc install
[[ $target_cpu =~ ^[a-zA-Z0-9_.+-]+$ ]] || { fail 'Invalid target CPU'; exit 2; }
for value in "$passes" "$rounds" "$iterations" "$limit"; do positive "$value" || { fail 'Workload counts must be positive integers'; exit 2; }; done
((passes<=100 && rounds<=99 && iterations<=10000)) || { fail 'Workload count exceeds benchmark limits'; exit 2; }
[[ -n $cpu ]] || cpu=$(allowed_cpu_ids | sed -n '1p')
check_cpu "$cpu"
IFS=, read -ra backends <<<"$hashing"
[[ $hashing == portable || $hashing == assembly || $hashing == portable,assembly || $hashing == assembly,portable ]] || { fail 'Select portable, assembly or both'; exit 2; }
BENCH_BUILD=${VERIFIER_BUILD:-$BENCH_ROOT/benchmarks/build/linux/verifier-$target_cpu}
cd -- "$BENCH_ROOT"
plan=$(jq -n --arg toolchain "$toolchain" --arg target_cpu "$target_cpu" --arg hashing "$hashing" \
    --argjson cpu "$cpu" --argjson passes "$passes" --argjson rounds "$rounds" --argjson iterations "$iterations" \
    '{toolchain:$toolchain,target_cpu:$target_cpu,hashing:($hashing|split(",")),cpu:$cpu,passes:$passes,rounds:$rounds,iterations:$iterations}')
if [[ $action == plan ]]; then printf '%s\n' "$plan"; exit 0; fi

report() {
    [[ -n $session && -f $session/metadata.json ]] || { fail 'Report requires a completed session'; return 1; }
    local -a raw=("$session"/pass-*.json)
    [[ -f ${raw[0]} ]] || { fail 'No raw measurements'; return 1; }
    jq -es '
      def median: sort | length as $n | (.[(($n-1)/2|floor)]+.[$n/2|floor])/2;
      .[0] as $meta | .[1:] as $runs |
      if ($runs|length) != ($meta.plan.passes*($meta.plan.hashing|length)) then error("Incomplete campaign") else . end |
      if ([$runs[]|[.hashing_backend,.process_pass]]|sort) != ([$meta.plan.hashing[] as $b|range(1;$meta.plan.passes+1)|[$b,.]]|sort) then error("Missing or duplicated process") else . end |
      if all($runs[];
        .schema_version==1 and .rounds==$meta.plan.rounds and .iterations==$meta.plan.iterations and
        .reference_revision==$meta.reference_revision and (.cases|length)==4 and
        ([.cases[].name]|sort)==["leaf decode + verify","leaf verify","recursive decode + verify","recursive verify"] and
        all(.cases[]; (.samples|length)==($meta.plan.rounds*$meta.plan.iterations) and
          [.samples[]|[.round,.iteration]]==[range($meta.plan.rounds) as $r|range($meta.plan.iterations)|[$r,.]] and
          all(.samples[]; .local_ns>0 and .reference_ns>0))) then . else error("Invalid or incomplete raw samples") end |
      [$runs[]|.hashing_backend as $backend|.process_pass as $pass|.cases[]|
        .name as $name|.samples|group_by(.round)[]|
        {backend:$backend,name:$name,pass:$pass,local_ns:(map(.local_ns)|add/length),reference_ns:(map(.reference_ns)|add/length)}] as $blocks |
      {schema_version:1,metadata:$meta,raw:$runs,summary:($blocks|group_by([.backend,.name])|map({
        backend:.[0].backend,name:.[0].name,blocks:length,
        local_ms:(map(.local_ns)|median/1000000), reference_ms:(map(.reference_ns)|median/1000000),
        paired_time_reduction_percent:(map(100*(1-.local_ns/.reference_ns))|median)}))}
    ' "$session/metadata.json" "${raw[@]}" >"$session/measurements.json"
    {
        printf '# Aggregate verifier benchmark\n\n'
        jq -r '.metadata.machine_before|"CPU: \(.model_name); \(.platform); logical CPU \(.logical_cpu)."' "$session/measurements.json"
        printf '\n| Hashing | Case | Local (ms) | Reference (ms) | Paired time reduction |\n| --- | --- | ---: | ---: | ---: |\n'
        jq -r '.summary[]|"| \(.backend) | \(.name) | \(.local_ms*1000|round|./1000) | \(.reference_ms*1000|round|./1000) | \(.paired_time_reduction_percent*10|round|./10)% |"' "$session/measurements.json"
        printf '\nMedian of per-round means across fresh processes. Each call uses the same proof and claims in both implementations; call order alternates.\n'
    } >"$session/README-benchmarks.md"
    cat "$session/README-benchmarks.md"
}
if [[ $action == report ]]; then report; exit 0; fi
mkdir -p -- "$BENCH_BUILD"
exec {build_lock}>"$BENCH_BUILD/build.lock"
flock -n "$build_lock" || { fail 'Another verifier build owns this directory'; exit 1; }
source_state=$(source_snapshot crates/lean-verifier benchmarks/verifier.sh)
builds='{}'
for backend in "${backends[@]}"; do
    features=(); [[ $backend != assembly ]] || features=(--features lean-verifier/asm-keccak)
    command=(env -u CARGO_ENCODED_RUSTFLAGS -u SHA3_ASM_SCRIPT "RUSTFLAGS=-C target-cpu=$target_cpu" \
        "CARGO_TARGET_DIR=$BENCH_BUILD/cargo" CARGO_PROFILE_BENCH_LTO=thin CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 CARGO_PROFILE_BENCH_OPT_LEVEL=3 CARGO_PROFILE_BENCH_INCREMENTAL=false)
    graph=$("${command[@]}" cargo "+$toolchain" metadata --locked --format-version 1 --manifest-path "$BENCH_ROOT/crates/lean-verifier/Cargo.toml" --no-default-features "${features[@]}")
    graph=$(jq -c '(.resolve.nodes|map({key:.id,value:.features})|from_entries) as $features|[.packages[]|{name,version,source,features:$features[.id]}]' <<<"$graph")
    jq -e 'all(.[];.name!="alloy-primitives" or (.features|index("keccak-cache-global")|not))' <<<"$graph" >/dev/null
    command+=(cargo "+$toolchain" build -p lean-verifier --profile bench --locked --bench verify --no-default-features "${features[@]}" --message-format=json-render-diagnostics)
    printf 'Building aggregate verifier (%s)\n' "$backend" >&2
    "${command[@]}" >"$BENCH_BUILD/$backend.build.stdout.log" 2>"$BENCH_BUILD/$backend.build.stderr.log" || { tail -n 35 "$BENCH_BUILD/$backend.build.stderr.log" >&2; exit 1; }
    executable=$(jq -ser '[.[]|select(.reason=="compiler-artifact" and .target.name=="verify" and .executable!=null)|.executable]|if length==1 then .[0] else error("Expected one verifier benchmark") end' "$BENCH_BUILD/$backend.build.stdout.log")
    install -m 755 -- "$executable" "$BENCH_BUILD/$backend"
    entry=$(jq -n --arg binary "$BENCH_BUILD/$backend" --arg sha256 "$(digest "$BENCH_BUILD/$backend")" --argjson graph "$graph" --argjson command "$(json_command "${command[@]}")" '{binary:$binary,binary_sha256:$sha256,resolved_cargo_features:$graph,command:$command}')
    builds=$(jq --arg backend "$backend" --argjson entry "$entry" '.+{($backend):$entry}' <<<"$builds")
done
[[ $(jq -r .source_sha256 <<<"$source_state") == "$(source_snapshot crates/lean-verifier benchmarks/verifier.sh | jq -r .source_sha256)" ]] || { fail 'Sources changed during compilation'; exit 1; }
[[ $action != build ]] || exit 0
session=${session:-$BENCH_ROOT/benchmarks/results/verifier-$(date -u +%Y%m%dT%H%M%SZ)}
session=$(realpath -m -- "$session")
[[ ! -e $session ]] || { fail 'Session already exists; choose another path'; exit 1; }
mkdir -p -- "$session"
lock_cpus "$cpu"
machine=$(machine_snapshot "$cpu")
atomic_json "$session/metadata.json" -n --argjson plan "$plan" --argjson source "$source_state" --argjson builds "$builds" \
    --argjson machine "$machine" --arg rustc "$(rustc "+$toolchain" -vV)" --arg cc "$("${CC:-cc}" --version | head -n 1)" \
    --arg reference "$(jq -r .revision crates/lean-verifier/reference.json)" \
    '{plan:$plan,source:$source,builds:$builds,machine_before:$machine,rustc:$rustc,cc:$cc,reference_revision:$reference,profile:{opt_level:3,lto:"thin",codegen_units:1}}'
for ((pass=1;pass<=passes;pass++)); do
    # Alternate build order across fresh processes; each process also alternates native calls.
    for ((i=0;i<${#backends[@]};i++)); do
        backend=${backends[$(( (i+pass-1)%${#backends[@]} ))]}
        printf -v stem '%s/pass-%02d-%s' "$session" "$pass" "$backend"
        printf 'Measuring aggregate verifier (%s, process %s/%s)\n' "$backend" "$pass" "$passes" >&2
        [[ $(digest "$BENCH_BUILD/$backend") == "$(jq -r --arg backend "$backend" '.[$backend].binary_sha256' <<<"$builds")" ]] || { fail 'Benchmark binary changed'; exit 1; }
        run_logged "$stem" "$cpu" "$limit" "$BENCH_BUILD/$backend" --json --rounds "$rounds" --iterations "$iterations"
        atomic_json "$stem.json" --arg backend "$backend" --argjson pass "$pass" '.+{hashing_backend:$backend,process_pass:$pass}' "$stem.stdout.log"
    done
done
after=$(machine_snapshot "$cpu")
require_same_machine "$machine" "$after"
[[ $(jq -r .source_sha256 <<<"$source_state") == "$(source_snapshot crates/lean-verifier benchmarks/verifier.sh | jq -r .source_sha256)" ]] || { fail 'Sources changed during measurement'; exit 1; }
atomic_json "$session/metadata.json" --argjson after "$after" '.+{machine_after:$after}' "$session/metadata.json"
report
printf 'Results: %s/measurements.json\n' "$session"
