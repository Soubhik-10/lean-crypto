#!/usr/bin/env bash
# Shared Linux benchmark operations. Sourcing this file starts no measurements.
BENCH_ROOT=${BENCH_ROOT:-$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)}
BENCH_BUILD=${BENCH_BUILD:-$BENCH_ROOT/benchmarks/build/linux}
BENCH_RESULTS=${BENCH_RESULTS:-$BENCH_ROOT/benchmarks/results/linux}
export LC_ALL=C

fail() { printf 'error: %s\n' "$*" >&2; return 1; }
need() { local name; for name in "$@"; do command -v "$name" >/dev/null || { fail "Missing command: $name"; return 1; }; done; }
linux_requirements() {
    [[ $(uname -s) == Linux ]] || { fail 'Use Linux or WSL.'; return 1; }
    need bash jq awk sha256sum taskset flock timeout setsid realpath git sort date
}
utc() { date -u +%Y-%m-%dT%H:%M:%SZ; }
digest() { sha256sum -- "$1" | cut -d ' ' -f 1; }
integer() { [[ $1 =~ ^(0|[1-9][0-9]{0,8})$ ]]; }
positive() { integer "$1" && ((10#$1 > 0)); }
json_array() { if (($#)); then printf '%s\n' "$@" | jq -Rsc 'split("\n")[:-1]'; else printf '[]\n'; fi; }
json_command() { json_array "$@"; }
atomic_json() {
    local destination=$1; shift
    local temporary=${destination}.tmp.$BASHPID
    mkdir -p -- "$(dirname -- "$destination")"
    if jq "$@" >"$temporary"; then mv -f -- "$temporary" "$destination"; else rm -f -- "$temporary"; return 1; fi
}
allowed_cpu_ids() {
    local list range first last cpu; local -a ranges
    list=$(awk '/^Cpus_allowed_list:/ { print $2 }' /proc/self/status)
    IFS=, read -ra ranges <<<"$list"
    for range in "${ranges[@]}"; do
        first=${range%-*}; last=${range#*-}
        for ((cpu=first; cpu<=last; cpu++)); do printf '%s\n' "$cpu"; done
    done
}
physical_cpu_ids() {
    local cpu socket core; local -A seen=()
    while read -r cpu; do
        socket=$(<"/sys/devices/system/cpu/cpu$cpu/topology/physical_package_id")
        core=$(<"/sys/devices/system/cpu/cpu$cpu/topology/core_id")
        if [[ ! ${seen[$socket:$core]+present} ]]; then
            seen[$socket:$core]=1; printf '%s\n' "$cpu"
        fi
    done < <(allowed_cpu_ids)
}
check_cpu() { integer "$1" && allowed_cpu_ids | grep -Fx -- "$1" >/dev/null || { fail "CPU $1 is outside the process CPU allocation"; return 1; }; }
lock_cpus() {
    local cpu fd; local -a ids
    mkdir -p -- "$BENCH_ROOT/benchmarks/build"
    IFS=, read -ra ids <<<"$1"
    for cpu in "${ids[@]}"; do
        check_cpu "$cpu" || return 1
        exec {fd}>"$BENCH_ROOT/benchmarks/build/cpu-$cpu.lock"
        flock -n "$fd" || { fail "Another benchmark owns CPU $cpu"; return 1; }
        # Leave each descriptor open until this process exits.
    done
}
cpu_capabilities() {
    local toolchain=$1 probe=$BENCH_BUILD/probe/host-probe
    mkdir -p -- "$(dirname -- "$probe")"
    rustc "+$toolchain" --edition 2024 "$BENCH_ROOT/benchmarks/suite/host_probe.rs" -o "$probe"
    "$probe"
}
source_snapshot() {
    local files='{}' name hash revision changes
    revision=$(git -C "$BENCH_ROOT" rev-parse HEAD)
    changes=$(git -C "$BENCH_ROOT" status --porcelain --untracked-files=no)
    while IFS= read -r -d '' name; do
        [[ -f $BENCH_ROOT/$name ]] || continue
        hash=$(digest "$BENCH_ROOT/$name")
        files=$(jq -c --arg name "$name" --arg hash "$hash" '.+{($name):$hash}' <<<"$files")
    done < <(git -C "$BENCH_ROOT" ls-files -z --cached --others --exclude-standard -- \
        Cargo.toml Cargo.lock crates/lean-sphincs benchmarks/evm2 benchmarks/suite benchmarks/run.sh benchmarks/compare.sh benchmarks/prover "$@")
    hash=$(printf '%s' "$(jq -cS . <<<"$files")" | sha256sum | cut -d ' ' -f 1)
    jq -n --arg revision "$revision" --arg changes "$changes" --arg hash "$hash" --argjson files "$files" \
        '{revision:$revision,tracked_changes:($changes!=""),source_sha256:$hash,files:$files}'
}
machine_snapshot() {
    local cpu=${1:-0} model cores logical governor minimum maximum
    model=$(awk -F ': *' '/^model name/ {print $2;exit}' /proc/cpuinfo)
    [[ -n $model ]] || model=$(uname -m)
    cores=$(physical_cpu_ids | wc -l); logical=$(allowed_cpu_ids | wc -l)
    governor=null; minimum=null; maximum=null
    [[ ! -r /sys/devices/system/cpu/cpu$cpu/cpufreq/scaling_governor ]] || governor=$(jq -Rn --arg v "$(<"/sys/devices/system/cpu/cpu$cpu/cpufreq/scaling_governor")" '$v')
    [[ ! -r /sys/devices/system/cpu/cpu$cpu/cpufreq/scaling_min_freq ]] || minimum=$(<"/sys/devices/system/cpu/cpu$cpu/cpufreq/scaling_min_freq")
    [[ ! -r /sys/devices/system/cpu/cpu$cpu/cpufreq/scaling_max_freq ]] || maximum=$(<"/sys/devices/system/cpu/cpu$cpu/cpufreq/scaling_max_freq")
    jq -n --arg captured "$(utc)" --arg platform "$(uname -srm)" --arg model "$model" \
        --argjson cpu "$cpu" --argjson cores "$cores" --argjson logical "$logical" \
        --argjson governor "$governor" --argjson minimum "$minimum" --argjson maximum "$maximum" \
        '{captured_utc:$captured,platform:$platform,logical_cpu:$cpu,model_name:$model,
          processors:[{Name:$model,NumberOfCores:$cores,NumberOfLogicalProcessors:$logical}],
          scaling_governor:$governor,scaling_min_freq:$minimum,scaling_max_freq:$maximum,
          frequency_note:"OS frequency limits are not measured effective clocks"}'
}
require_same_machine() {
    local fields='{platform,logical_cpu,processors,scaling_governor,scaling_min_freq,scaling_max_freq}'
    [[ $(jq -cS "$fields" <<<"$1") == "$(jq -cS "$fields" <<<"$2")" ]] || { fail 'CPU allocation or machine conditions changed; start a new session'; return 1; }
}
# taskset applies affinity before exec; the native binary additionally waits for stdin.
# setsid lets interruption terminate the process group, including recursive children.
run_logged() (
    local stem=$1 cpus=$2 limit=$3; shift 3
    local child status=0; local -a command=(setsid)
    mkdir -p -- "$(dirname -- "$stem")"
    if ((limit>0)); then command+=(timeout --signal=TERM --kill-after=10s "$limit"); fi
    command+=(taskset --cpu-list "$cpus" "$@")
    trap 'trap - INT TERM EXIT; if [[ ${child:-} ]]; then kill -TERM -- "-$child" 2>/dev/null || true; wait "$child" 2>/dev/null || true; fi' EXIT
    trap 'exit 130' INT; trap 'exit 143' TERM
    "${command[@]}" >"$stem.stdout.log" 2>"$stem.stderr.log" <<<'start' &
    child=$!
    wait "$child" || status=$?
    ((status==0)) || { fail "Command exited $status; inspect $stem.stderr.log"; return "$status"; }
    child=
)
archive_attempt() {
    local session=$1 task=$2 destination path
    local -a files=()
    shopt -s nullglob
    files=("$session/$task".*)
    ((${#files[@]})) || return 0
    destination=$session/attempts/$task-$(date +%s%N)
    mkdir -p -- "$destination"
    for path in "${files[@]}"; do
        [[ -f $path && $(dirname -- "$(realpath -- "$path")") == "$session" ]] || { fail 'Unsafe attempt path'; return 1; }
        mv -- "$path" "$destination/"
    done
}
validate_native_report() {
    jq -e --argjson count "$2" '
      .schema_version==1 and .status=="complete" and (.measurements|length)>0 and
      ([.measurements[].name]|length== (unique|length)) and
      all(.measurements[]; . as $measurement |
        .calibrated_iterations>0 and .work_items_per_iteration>0 and
        (.samples|length)==$count and [.samples[].index]==[range($count)] and
        all(.samples[]; .iterations==$measurement.calibrated_iterations and
          .work_items==(.iterations*$measurement.work_items_per_iteration) and .work_items>0 and .elapsed_ns>0 and
          ((.elapsed_ns/.work_items-.ns_per_op)|fabs)<=((.ns_per_op|fabs)*1e-12)))
    ' "$1" >/dev/null || { fail "Incomplete or inconsistent report: $1"; return 1; }
}
