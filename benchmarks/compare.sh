#!/usr/bin/env bash
# Focused presets over the existing build/run/report suite.
set -Eeuo pipefail
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
ROOT=$(cd -- "$HERE/.." && pwd -P)

usage() {
    cat <<'HELP'
Usage: bash benchmarks/compare.sh [native|backends|hashes] [plan|build|run|report] [options]
Default: native run (builds, measures, then reports).
  native    Our native APIs, unmodified leanVM and C-backed evm2 ecrecover
  backends  Also compare RustCrypto/assembly hashing and evm2 k256 recovery
  hashes    Isolated Alloy/upstream hash kernels across input sizes
  --session PATH      Output directory; required for report or --resume
  --cpu N             Pin to an allowed logical CPU (default: first allowed)
  --cc PROGRAM        C compiler executable (default: CC or cc)
  --samples N         Samples per process (native/backends: 44; hashes: 30)
  --passes N          Fresh processes per configuration (default: 3)
  --sample-ms N       Adaptive batch target (default: 20 ms)
  --cooldown-seconds N  Delay between processes
  --timeout SECONDS   Per-binary timeout; 0 means no limit
  --bootstrap N       Report resamples (default: 2000)
  --resume            Resume validated tasks without rebuilding
Requires Linux/WSL and the tooling in benchmarks/SUITE.md.
HELP
}

[[ ${1-} != --help && ${1-} != -h ]] || { usage; exit 0; }
preset=native; action=run
if (($#)) && [[ $1 != --* ]]; then preset=$1; shift; fi
if (($#)) && [[ $1 != --* ]]; then action=$1; shift; fi
case "$preset" in
    native) options=(--profile raw --targets native --hashing assembly --recovery libsecp256k1 --groups direct,ecrecover --samples 44 --passes 3 --sample-ms 20);;
    backends) options=(--profile raw --targets native --hashing portable,assembly --recovery libsecp256k1,k256 --groups direct,ecrecover --samples 44 --passes 3 --sample-ms 20);;
    hashes) options=(--profile hashes --targets native --hashing portable,assembly --recovery libsecp256k1 --groups hash --samples 30 --passes 3 --sample-ms 20);;
    *) printf 'error: unknown preset: %s\n' "$preset" >&2; usage >&2; exit 2;;
esac
case "$action" in plan|build|run|report) ;; *) printf 'error: unknown action: %s\n' "$action" >&2; exit 2;; esac
session=; resume=false; compiler=${CC:-cc}; bootstrap=2000
while (($#)); do
    case "$1" in
        --session|--cc|--bootstrap|--cpu|--samples|--passes|--sample-ms|--cooldown-seconds|--timeout)
            (($#>=2)) || { printf 'error: missing value for %s\n' "$1" >&2; exit 2; }
            case "$1" in
                --session) session=$2;; --cc) compiler=$2;; --bootstrap) bootstrap=$2;;
                *) options+=("$1" "$2");;
            esac
            shift 2;;
        --resume) resume=true; shift;;
        --help|-h) usage; exit 0;;
        *) printf 'error: unknown option: %s\n' "$1" >&2; exit 2;;
    esac
done
if [[ $resume == true && ( $action != run || -z $session ) ]]; then
    printf 'error: --resume requires run and an explicit --session\n' >&2; exit 2
fi
if ! [[ $bootstrap =~ ^(0|[1-9][0-9]{0,8})$ ]] || ((bootstrap<100 || bootstrap>100000)); then
    printf 'error: --bootstrap must be between 100 and 100000\n' >&2; exit 2
fi
cd -- "$ROOT"
if [[ $action == report ]]; then
    [[ -n $session ]] || { printf 'error: report requires --session\n' >&2; exit 2; }
    exec bash "$HERE/run.sh" report --session "$session" --bootstrap "$bootstrap"
fi
export CC=$compiler
compiler_id=${compiler##*/}; compiler_id=${compiler_id//[^a-zA-Z0-9_.-]/_}
export BENCH_BUILD=${BENCH_BUILD:-$ROOT/benchmarks/build/linux/compare-$preset-$compiler_id}
if [[ $action == plan ]]; then exec bash "$HERE/run.sh" plan "${options[@]}"; fi
if [[ $resume != true ]]; then
    command -v -- "$CC" >/dev/null || { printf 'error: C compiler not found: %s\n' "$CC" >&2; exit 2; }
    compiler_version=$("$CC" --version)
    printf 'C compiler: %s\n' "${compiler_version%%$'\n'*}" >&2
    bash "$HERE/run.sh" build "${options[@]}"
fi
[[ $action != build ]] || exit 0
session=${session:-benchmarks/results/compare-$preset-$(date -u +%Y%m%dT%H%M%SZ)}
run_options=(--session "$session"); [[ $resume != true ]] || run_options+=(--resume)
bash "$HERE/run.sh" run "${options[@]}" "${run_options[@]}"
bash "$HERE/run.sh" report --session "$session" --bootstrap "$bootstrap"
printf 'Results: %s/README-benchmarks.md\n' "$session"
