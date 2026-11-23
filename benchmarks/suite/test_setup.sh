#!/usr/bin/env bash
set -Eeuo pipefail
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
ROOT=$(cd -- "$HERE/.." && pwd -P)
source "$HERE/suite/common.sh"
linux_requirements
TEST_DIR=$(mktemp -d "${TMPDIR:-/tmp}/lean-sphincs shell.XXXXXXXX")
# Remove only explicitly created test files; keep the directory for failed-test diagnosis.
trap 'if [[ ${KEEP_BENCH_TEST_FILES:-0} != 1 ]]; then find "$TEST_DIR" -depth -type f -delete; find "$TEST_DIR" -depth -type d -empty -delete; fi' EXIT
checks=0
ok() { checks=$((checks+1)); printf 'ok %d - %s\n' "$checks" "$1"; }
expect_failure() { if "$@" >"$TEST_DIR/rejected.out" 2>"$TEST_DIR/rejected.err"; then fail "Unexpected success: $*"; return 1; fi; }
capabilities=$(jq -n --slurpfile config "$HERE/suite/config.json" '{architecture:"x86_64",features:($config[0].targets|map(.requires[])|unique|map({key:.,value:true})|from_entries)}')
plan() {
    local profile=raw targets= hashing= recovery= groups=direct,ecrecover samples= sample_ms= passes= cooldown= cpu=0
    local disable_slp=false unmodified_tiny=false per_fixture=false
    source "$HERE/run.sh"
    native_plan "$capabilities"
}
plan >"$TEST_DIR/plan.json"
jq -e '(.jobs|length)==30 and ([.jobs[].case_count]|add)==120 and
  ([.jobs[]|select(.id|endswith("-no-slp"))]|length)==6 and
  all(.jobs[];if .ecrecover=="k256" then .groups==["ecrecover"] else true end)' "$TEST_DIR/plan.json" >/dev/null
ok 'Full matrix, recovery-only jobs and tiny-keccak SLP controls'
(
    source "$HERE/run.sh"
    profile=raw; targets=baseline,v2,v3,v4,native; hashing=portable; recovery=libsecp256k1; groups=direct
    samples=; sample_ms=; passes=; cooldown=; cpu=0; disable_slp=false;unmodified_tiny=false;per_fixture=false
    native_plan '{"architecture":"x86_64","features":{"sse2":true}}' >"$TEST_DIR/minimal.json"
    jq -e '(.jobs|length)==2 and (.skipped|length)==3' "$TEST_DIR/minimal.json" >/dev/null
    native_plan '{"architecture":"aarch64","features":{}}' >"$TEST_DIR/arm.json"
    jq -e '(.jobs|length)==1 and .jobs[0].target.id=="native" and (.skipped|length)==4' "$TEST_DIR/arm.json" >/dev/null
)
ok 'Unsupported ISA skipping and native ARM planning'
for bad in 'plan --targets unknown' 'plan --groups typo' 'plan --samples 5' 'plan --hashing tiny,tiny'; do
    # Exercise the parser with a stub probe; no compiler or benchmark is started.
    expect_failure bash -c 'set -Eeuo pipefail; source "$1/run.sh"; STUB_CAPS=$2; cpu_capabilities(){ printf "%s\n" "$STUB_CAPS"; }; read -ra options <<<"$3"; main "${options[@]}"' _ "$HERE" "$capabilities" "$bad"
done
ok 'Invalid targets, groups, corpus weighting and duplicate selections rejected'
(
    source "$HERE/prover/run.sh"
    preset=quick;target=native;revisions=;provers=;threads=;workloads=;repeat=;rate=
    physical_cpu_ids(){ printf '%s\n' {0..15}; }
    prover_plan "$capabilities" >"$TEST_DIR/prover-plan.json"
    jq -e '(.jobs|length)==24 and ([.jobs[].prover]|unique)==["experimental","stable"] and .repeat==5' "$TEST_DIR/prover-plan.json" >/dev/null
    physical_cpu_ids(){ printf '%s\n' 0 1; }
    prover_plan "$capabilities" >"$TEST_DIR/small-host.json"
    jq -e '([.jobs[].threads]|unique)==[1,2]' "$TEST_DIR/small-host.json" >/dev/null
    fixture_counts <"$TEST_DIR/prover-plan.json" >"$TEST_DIR/counts.json"
    jq -e '.sphincs==32 and .xmss==128' "$TEST_DIR/counts.json" >/dev/null
)
expect_failure bash "$HERE/prover/run.sh" run
ok 'Prover matrix, adaptive workers, recursive cache scope and execution gate'
jq -n '{stdout:"proof size : 220.4 KiB\nproving time : 1.234 s  peak memory 3.25 GiB\nverifying : 4.21 ms\n",stderr:"passes : 1.235 s  1.233 s  1.234 s\n"}' >"$TEST_DIR/cli.json"
jq --argjson repeat 3 -f "$HERE/prover/parse.jq" "$TEST_DIR/cli.json" >"$TEST_DIR/metrics.json"
jq -e '.proof_samples_s==[1.235,1.233,1.234] and .sample_precision_s==0.001 and .reported_proof_size_kib==220.4' "$TEST_DIR/metrics.json" >/dev/null
expect_failure jq --argjson repeat 5 -f "$HERE/prover/parse.jq" "$TEST_DIR/cli.json"
ok 'Stock CLI parsing retains every pass and rejects partial reports'
for p in 1 2; do for i in {1..20}; do printf 'example\tconstant\t%s\t100\n' "$p"; done; done >"$TEST_DIR/stats.tsv"
awk -v resamples=100 -v seed=42 -f "$HERE/suite/stats.awk" "$TEST_DIR/stats.tsv" >"$TEST_DIR/stats-a.json"
awk -v resamples=100 -v seed=42 -f "$HERE/suite/stats.awk" "$TEST_DIR/stats.tsv" >"$TEST_DIR/stats-b.json"
cmp "$TEST_DIR/stats-a.json" "$TEST_DIR/stats-b.json"
jq -e '.median_ns==100 and .median_ci95_ns==[100,100] and .samples==40 and .outliers_removed==0' "$TEST_DIR/stats-a.json" >/dev/null
printf 'example\tconstant\t2\t1000000000\n' >>"$TEST_DIR/stats.tsv"
awk -v resamples=100 -v seed=42 -f "$HERE/suite/stats.awk" "$TEST_DIR/stats.tsv" | jq -e '.samples==41 and .max_ns==1000000000 and .outliers_removed==0' >/dev/null
ok 'Repeatable block bootstrap, exact constant intervals and retained outliers'
jq -n '{schema_version:2,sampling:{passes:2,samples_per_case:5,outliers_removed:0},cpu:{Name:"Synthetic CPU"},rustc:"rustc synthetic",reference_revision:"synthetic",
  configurations:{example:{configuration:{target:{id:"native"},keccak:"tiny",ecrecover:"k256"},rustflags:["-C","no-vectorize-slp"]}},
  measurements:[{configuration:"example",operation:"direct/lean-sphincs/verify",passes:[
    {pass:1,iterations:2,work_items_per_iteration:4,elapsed_ns:[8,16,24,32,808]},
    {pass:2,iterations:1,work_items_per_iteration:2,elapsed_ns:[8,10,12,14,16]}]}]}' >"$TEST_DIR/published.json"
jq -r -f "$HERE/suite/normalize.jq" "$TEST_DIR/published.json" | awk -v resamples=100 -f "$HERE/suite/stats.awk" | \
    jq -e '.median_ns==4.5 and .samples==10 and .pass_medians_ns==[3,6]' >/dev/null
jq '.measurements[0].passes[1].elapsed_ns|=.[1:]' "$TEST_DIR/published.json" >"$TEST_DIR/partial.json"
expect_failure jq -r -f "$HERE/suite/normalize.jq" "$TEST_DIR/partial.json"
jq '.measurements[0].passes[1].pass=1' "$TEST_DIR/published.json" >"$TEST_DIR/duplicate-pass.json"
expect_failure jq -r -f "$HERE/suite/normalize.jq" "$TEST_DIR/duplicate-pass.json"
ok 'Published batch denominators and pass/sample completeness'
jq '(.measurements[].passes[].elapsed_ns[]) *= 1000' "$TEST_DIR/published.json" >"$TEST_DIR/human-readable.json"
BENCH_RESULTS=$TEST_DIR/results bash "$HERE/run.sh" report --measurements "$TEST_DIR/human-readable.json" --bootstrap 100 --no-reference >"$TEST_DIR/report.out"
grep -F '| native | tiny-keccak | disabled | 4.50 |' "$TEST_DIR/results/published/human-readable/README-benchmarks.md" >/dev/null
! grep -F 'leanVM, unmodified (' "$TEST_DIR/results/published/human-readable/README-benchmarks.md" >/dev/null
ok 'Linux report generation without executing a binary'
# A synthetic executable checks affinity before replying to the start gate.
cat >"$TEST_DIR/gated" <<'GATED'
#!/usr/bin/env bash
set -euo pipefail
IFS= read -r message
[[ $message == start ]]
[[ $(awk '/^Cpus_allowed_list:/{print $2}' /proc/self/status) == "$EXPECTED_CPU" ]]
printf 'affinity verified\n'
GATED
chmod +x "$TEST_DIR/gated"
mapfile -t available < <(allowed_cpu_ids)
EXPECTED_CPU=${available[0]};export EXPECTED_CPU
run_logged "$TEST_DIR/gated-result" "$EXPECTED_CPU" 5 "$TEST_DIR/gated"
grep -F 'affinity verified' "$TEST_DIR/gated-result.stdout.log" >/dev/null
ok 'Verified Linux CPU pinning before the child start gate'
# Timeout kills the command group, including a spawned child.
cat >"$TEST_DIR/slow" <<'SLOW'
#!/usr/bin/env bash
sleep 60 &
printf '%s\n' "$!" >"$CHILD_PID_FILE"
wait
SLOW
chmod +x "$TEST_DIR/slow"
export CHILD_PID_FILE=$TEST_DIR/child.pid
expect_failure bash -c 'set -Eeuo pipefail; source "$1/suite/common.sh"; run_logged "$2/timeout" "$3" 1 "$2/slow"' _ "$HERE" "$TEST_DIR" "$EXPECTED_CPU"
if [[ -f $CHILD_PID_FILE ]]; then
    child=$(<"$CHILD_PID_FILE")
    status=$(ps -o stat= -p "$child" 2>/dev/null || true)
    [[ -z $status || $status == Z* ]] || { fail 'Timeout left a running child'; exit 1; }
fi
ok 'Timeout cleans up child processes'
# Fake raw executable: exercise complete session/resume/report flows without crypto.
cat >"$TEST_DIR/fake-matrix" <<'FAKE'
#!/usr/bin/env bash
set -euo pipefail
samples=5;output=;corpus=
while (($#)); do
 case "$1" in
 --samples) samples=$2;shift 2;; --json) output=$2;shift 2;; --corpus-json) corpus=$2;shift 2;;
 --sample-ms|--warmup-ms|--seed|--extra-cases|--groups) shift 2;; --run|--wait-for-start) shift;; *) exit 2;;
 esac
done
read -r start;[[ $start == start ]]
printf 'call\n' >>"$MOCK_CALLS"
printf 'synthetic corpus\n' >"$corpus"
jq -n --argjson count "$samples" '{schema_version:1,status:"complete",
 build:{keccak_backend:"portable",ecrecover:"k256",experimental_adapter:false},
 measurements:[{name:"macro/evm2/ecrecover",calibrated_iterations:1,work_items_per_iteration:1,
 samples:[range($count)|{index:.,order:0,iterations:1,work_items:1,elapsed_ns:100,ns_per_op:100}]}]}' >"$output"
FAKE
chmod +x "$TEST_DIR/fake-matrix"
export TEST_HERE=$HERE TEST_SESSION=$TEST_DIR/session TEST_PLAN=$TEST_DIR/one-plan.json MOCK_CALLS=$TEST_DIR/calls
export BENCH_BUILD=$TEST_DIR/build BENCH_RESULTS=$TEST_DIR/results
mkdir -p -- "$BENCH_BUILD"
jq --argjson cpu "$EXPECTED_CPU" '.jobs|=map(select(.id=="baseline-portable-k256")) |
 .cpu=$cpu|.profile.samples=5|.profile.passes=1|.cooldown_seconds=0' "$TEST_DIR/plan.json" >"$TEST_PLAN"
snapshot=$(source_snapshot)
jq -n --argjson source "$snapshot" --slurpfile plan "$TEST_PLAN" --arg binary "$TEST_DIR/fake-matrix" --arg hash "$(digest "$TEST_DIR/fake-matrix")" '
 {schema_version:2,source:$source,rustc:"rustc synthetic",jobs:{"baseline-portable-k256":{
 configuration:$plan[0].jobs[0],binary:$binary,binary_sha256:$hash,rustflags:["-C","target-cpu=x86-64"],
 build:{build:{keccak_backend:"portable",ecrecover:"k256",experimental_adapter:false}},
 resolved_cargo_features:[{name:"lean_sphincs",source:"git+https://example.invalid/source#synthetic",features:[]}],
 profile:{optimization:3,lto:"thin",codegen_units:1,incremental:false},cflags:{}}}}' >"$BENCH_BUILD/builds.json"
cat >"$TEST_DIR/session-driver" <<'DRIVER'
#!/usr/bin/env bash
set -Eeuo pipefail
source "$TEST_HERE/run.sh"
rustc(){ printf 'rustc synthetic\n'; }
cpu=$(jq -r .cpu "$TEST_PLAN");session=$TEST_SESSION;timeout_seconds=5;resume=$1
run_native "$(cat "$TEST_PLAN")"
DRIVER
bash "$TEST_DIR/session-driver" false >"$TEST_DIR/session.out"
bash "$TEST_DIR/session-driver" true >>"$TEST_DIR/session.out"
[[ $(wc -l <"$MOCK_CALLS") == 1 ]]
jq -e '.finished_utc!=null and (.completed|length)==1' "$TEST_SESSION/session.json" >/dev/null
bash "$HERE/run.sh" report --session "$TEST_SESSION" --bootstrap 100 >"$TEST_DIR/session-report.out"
jq -e 'length==1 and .[0].median_ns==100 and .[0].samples==5' "$TEST_SESSION/summary.json" >/dev/null
ok 'Completed sessions resume without executing again and produce reports'
raw=$TEST_SESSION/pass-01-baseline-portable-k256.json
cp -- "$raw" "$TEST_DIR/raw-backup.json"
printf '\n' >>"$raw"
expect_failure bash "$TEST_DIR/session-driver" true
grep -F 'Completed raw data changed' "$TEST_DIR/rejected.err" >/dev/null
cp -- "$TEST_DIR/raw-backup.json" "$raw"
cp -- "$TEST_DIR/fake-matrix" "$TEST_DIR/binary-backup"
printf '\n# changed binary\n' >>"$TEST_DIR/fake-matrix"
expect_failure bash "$TEST_DIR/session-driver" true
grep -F 'Binary hash changed' "$TEST_DIR/rejected.err" >/dev/null
cp -- "$TEST_DIR/binary-backup" "$TEST_DIR/fake-matrix"
cp -- "$BENCH_BUILD/builds.json" "$TEST_DIR/builds-backup.json"
jq '.source.source_sha256="changed"' "$TEST_DIR/builds-backup.json" >"$BENCH_BUILD/builds.json"
expect_failure bash "$TEST_DIR/session-driver" true
grep -F 'Source or compiler changed' "$TEST_DIR/rejected.err" >/dev/null
cp -- "$TEST_DIR/builds-backup.json" "$BENCH_BUILD/builds.json"
[[ $(wc -l <"$MOCK_CALLS") == 1 ]]
ok 'Resume rejects modified raw samples, binaries and source fingerprints'
jq '.measurements[0].samples[0].work_items=2' "$raw" >"$TEST_DIR/wrong-denominator.json"
expect_failure validate_native_report "$TEST_DIR/wrong-denominator.json" 5
cp -- "$TEST_SESSION/session.json" "$TEST_DIR/session-backup.json"
jq 'del(.finished_utc)' "$TEST_DIR/session-backup.json" >"$TEST_SESSION/session.json"
expect_failure bash "$HERE/run.sh" report --session "$TEST_SESSION" --bootstrap 100
ok 'Inconsistent timing denominators and unfinished sessions cannot be reported'
# A synthetic stock-CLI-shaped executable exercises the prover orchestration.
export MOCK_PROVER_CACHE=$TEST_DIR/prover-cache MOCK_PROVER_CALLS=$TEST_DIR/prover-calls
mkdir -p -- "$MOCK_PROVER_CACHE/current" "$MOCK_PROVER_CACHE/previous"
cat >"$TEST_DIR/fake-prover" <<'PROVER'
#!/usr/bin/env bash
set -euo pipefail
repeat=1
while (($#));do
 case "$1" in --repeat) repeat=$2;shift 2;; --prover|--cooldown|--log-inv-rate|--sphincs|--xmss) shift 2;; aggregate) shift;; *) exit 2;;esac
done
prefix=${0%/bin/leanvm};revision=${prefix##*/};revision=${revision%-native}
printf 'deterministic fixture bytes\n' >"$MOCK_PROVER_CACHE/$revision/lean_sphincs_signers_synthetic.bin"
printf 'call\n' >>"$MOCK_PROVER_CALLS"
printf 'proof size : 220.4 KiB\nproving time : 1.234 s  peak memory 3.25 GiB\nverifying : 4.21 ms\n'
printf 'passes :' >&2
for ((i=0;i<repeat;i++));do printf ' 1.234 s' >&2;done
printf '\n' >&2
PROVER
chmod +x "$TEST_DIR/fake-prover"
(
 source "$HERE/prover/run.sh"
 preset=quick;target=native;revisions=;provers=;threads=1;workloads=sphincs-16;repeat=3;rate=
 physical_cpu_ids(){ printf '%s\n' "$EXPECTED_CPU"; }
 prover_plan "$capabilities" >"$TEST_DIR/prover-one-plan.json"
)
export PROVER_TEST_PLAN=$TEST_DIR/prover-one-plan.json PROVER_TEST_SESSION=$TEST_DIR/prover-session
model=$(machine_snapshot "$EXPECTED_CPU"|jq -r .model_name)
for revision in current previous;do
 directory=$BENCH_BUILD/prover/$revision-native
 mkdir -p -- "$directory/bin"
 cp -- "$TEST_DIR/fake-prover" "$directory/bin/leanvm"
 sha=$(jq -r --arg revision "$revision" '.jobs[]|select(.revision==$revision)|.sha' "$PROVER_TEST_PLAN"|sort -u)
 jq -n --arg sha "$sha" --arg model "$model" --arg cache "$MOCK_PROVER_CACHE/$revision" --arg hash "$(digest "$directory/bin/leanvm")" \
  --argjson capabilities "$capabilities" '{sha:$sha,build_cpu_model:$model,capabilities:$capabilities,cache_directory:$cache,
  binary_sha256:$hash,rustc:"rustc synthetic",rustflags:["-C","target-cpu=native"],cargo_lock_sha256:"synthetic"}' >"$directory/build.json"
done
cat >"$TEST_DIR/prover-driver" <<'DRIVER'
#!/usr/bin/env bash
set -Eeuo pipefail
source "$TEST_HERE/prover/run.sh"
rustc(){ printf 'rustc synthetic\n'; }
session=$PROVER_TEST_SESSION;resume=$1;execute=true;timeout_seconds=5
run_provers "$(cat "$PROVER_TEST_PLAN")"
DRIVER
bash "$TEST_DIR/prover-driver" false >"$TEST_DIR/prover.out"
[[ $(wc -l <"$MOCK_PROVER_CALLS") == 6 ]]
bash "$TEST_DIR/prover-driver" true >>"$TEST_DIR/prover.out"
[[ $(wc -l <"$MOCK_PROVER_CALLS") == 6 ]]
bash "$HERE/prover/run.sh" report --session "$PROVER_TEST_SESSION" >"$TEST_DIR/prover-report.out"
jq -e 'length==4 and all(.[];.proving_mean_s==1.234)' "$PROVER_TEST_SESSION/summary.json" >/dev/null
ok 'Stock CLI invocation, matched caches, report export and no-op prover resume'
printf 'changed fixture\n' >"$MOCK_PROVER_CACHE/current/lean_sphincs_signers_synthetic.bin"
expect_failure bash "$TEST_DIR/prover-driver" true
grep -F 'Cached inputs changed' "$TEST_DIR/rejected.err" >/dev/null
printf 'deterministic fixture bytes\n' >"$MOCK_PROVER_CACHE/current/lean_sphincs_signers_synthetic.bin"
cp -- "$PROVER_TEST_SESSION/session.json" "$TEST_DIR/prover-session-backup.json"
jq '.fixture_cache_sha256={}|.completed={}|.complete=false' "$TEST_DIR/prover-session-backup.json" >"$PROVER_TEST_SESSION/session.json"
bash "$TEST_DIR/prover-driver" true >>"$TEST_DIR/prover.out"
[[ $(wc -l <"$MOCK_PROVER_CALLS") == 12 ]]
jq -e '.complete==true and (.completed|length)==4' "$PROVER_TEST_SESSION/session.json" >/dev/null
ok 'Modified cached inputs rejected; interrupted cache preparation can resume'

# Compare preset orchestration: planning never builds; resume/report never rebuild.
compare_root="$TEST_DIR/comparison fixture"
mkdir -p -- "$compare_root/benchmarks"
cp -- "$HERE/compare.sh" "$compare_root/benchmarks/compare.sh"
cat >"$compare_root/benchmarks/run.sh" <<'COMPARE_RUNNER'
#!/usr/bin/env bash
set -euo pipefail
jq -cn --arg cc "${CC-}" --args '{args:$ARGS.positional,cc:$cc}' -- "$@" >>"$COMPARE_CALLS"
COMPARE_RUNNER
cat >"$compare_root/compiler tool" <<'COMPARE_COMPILER'
#!/usr/bin/env bash
printf 'synthetic compiler 1.0\n'
COMPARE_COMPILER
chmod +x -- "$compare_root/compiler tool"
export COMPARE_CALLS="$TEST_DIR/compare-calls.jsonl"
compare_script="$compare_root/benchmarks/compare.sh"
bash "$compare_script" native plan --cc "$compare_root/compiler tool"
jq -se 'length==1 and .[0].args[0]=="plan" and (.[0].args|index("direct,ecrecover")!=null)' "$COMPARE_CALLS" >/dev/null
: >"$COMPARE_CALLS"
bash "$compare_script" backends --cc "$compare_root/compiler tool" --samples 88 --session 'results/a session' >"$TEST_DIR/compare.out"
jq -se 'map(.args[0])==["build","run","report"] and
  (.[0].args|index("portable,assembly")!=null) and
  (.[1].args|index("libsecp256k1,k256")!=null) and
  (.[1].args|index("results/a session")!=null) and
  (.[1].args|index("88")!=null)' "$COMPARE_CALLS" >/dev/null
: >"$COMPARE_CALLS"
bash "$compare_script" native --cc "$compare_root/compiler tool" --session 'results/a session' --resume >"$TEST_DIR/compare-resume.out"
jq -se 'map(.args[0])==["run","report"] and (.[0].args|index("--resume")!=null)' "$COMPARE_CALLS" >/dev/null
: >"$COMPARE_CALLS"
bash "$compare_script" native report --session 'results/a session'
jq -se 'map(.args[0])==["report"]' "$COMPARE_CALLS" >/dev/null
expect_failure bash "$compare_script" unknown plan
expect_failure bash "$compare_script" native report
expect_failure bash "$compare_script" native --resume
expect_failure bash "$compare_script" native --bootstrap invalid
expect_failure bash "$compare_script" native --bootstrap 99
[[ $(wc -l <"$COMPARE_CALLS") == 1 ]]
ok 'Comparison presets preserve arguments, gate execution and avoid rebuilding on resume/report'

# Aggregate report replay is pure data processing, and must fail closed on partial data.
verifier_dir="$TEST_DIR/verifier replay"
mkdir -p "$verifier_dir"
bash "$HERE/compare.sh" verifier plan --hashing portable --passes 1 --rounds 1 --iterations 1 >"$verifier_dir/plan.json"
jq -e '.hashing==["portable"] and .passes==1 and .rounds==1 and .iterations==1' "$verifier_dir/plan.json" >/dev/null
expect_failure bash "$HERE/compare.sh" verifier plan --hashing portable,portable
jq -n '{plan:{hashing:["portable"],passes:1,rounds:1,iterations:1},reference_revision:"fixture",
  machine_before:{model_name:"Synthetic CPU",platform:"test",logical_cpu:0}}' >"$verifier_dir/metadata.json"
expect_failure bash "$HERE/compare.sh" verifier report --session "$verifier_dir"
jq -n '{schema_version:1,reference_revision:"fixture",rounds:1,iterations:1,hashing_backend:"portable",process_pass:1,
 cases:(["leaf verify","leaf decode + verify","recursive verify","recursive decode + verify"]|map({name:.,samples:[{round:0,iteration:0,local_ns:100,reference_ns:200}]}))}' >"$verifier_dir/pass-01-portable.json"
bash "$HERE/compare.sh" verifier report --session "$verifier_dir" >"$verifier_dir/report.out"
jq -e '(.summary|length)==4 and all(.summary[];.local_ms==0.0001 and .reference_ms==0.0002 and .paired_time_reduction_percent==50)' "$verifier_dir/measurements.json" >/dev/null
cp "$verifier_dir/pass-01-portable.json" "$verifier_dir/pass-02-portable.json"
jq '.plan.passes=2' "$verifier_dir/metadata.json" >"$verifier_dir/meta.next"
mv "$verifier_dir/meta.next" "$verifier_dir/metadata.json"
expect_failure bash "$HERE/compare.sh" verifier report --session "$verifier_dir"
jq '.process_pass=2|.cases[0].samples=[]' "$verifier_dir/pass-01-portable.json" >"$verifier_dir/pass-02-portable.json"
expect_failure bash "$HERE/compare.sh" verifier report --session "$verifier_dir"
ok 'Verifier plans and report-only replay reject missing/duplicate processes and incomplete paired samples'

printf 'All %d shell setup checks passed; no cryptographic benchmarks ran.\n' "$checks"
