# Reproducible local benchmark suite

This suite prepares separate binaries for each CPU target and feature combination.
Planning, compilation and report generation are separate commands. Only the
explicit run command starts measurements. It never changes power plans, boost
settings, processor limits or system-wide affinity. The benchmark executable also requires an explicit measurement flag.

Use Python 3.11 or later and Rust 1.97.1. Git dependencies and both Cargo lockfiles
remain pinned. The library's minimum supported Rust version is unchanged.

## Matrix

The runner considers baseline x86-64, x86-64-v2, x86-64-v3, x86-64-v4 and the
host-native CPU target. A small baseline probe checks CPU and OS support before
optimized binaries may execute. Unsupported configurations are listed with their
missing capabilities.

Each target is built with RustCrypto, tiny-keccak and assembly Keccak, and with libsecp256k1
and k256 recovery providers. The alternate recovery provider normally receives
a recovery-only job because it does not select the signature implementation's
hashing backend. Exact Cargo features, compiler flags, source hashes, lockfiles,
binary hashes, C compiler settings and compiled backend selection are retained.

The pinned comparison package has no production Cargo feature switches.
Its scalar, vector and single-state accelerated paths are selected by compiler
target features. The binary description records AVX2, AVX-512, paired FORS
selection and actual batch width; labels are not inferred from the CPU name.

## Comparison contract

The tables compare complete native APIs using identical leanSPHINCS parameters,
secret seeds, messages and expected wire encodings. Verification starts with a
32-byte public key and a 7,740-byte signature. It includes leanVM's decoding into
its internal representation and this crate's in-place reads. Signing includes
signature serialization on both sides; key generation returns encoded public
keys on both sides. The separately measured parsed-verification diagnostic is
excluded from the main tables. No VM execution or proof generation is measured.

Both implementations are compiled into the same binary with the same target,
optimization and LTO settings. Any `no-vectorize-slp` setting applies to both.
The reference implementation is an unmodified pinned Git dependency. The
RustCrypto, tiny-keccak and asm-keccak labels select this crate's Alloy Keccak
implementation; they do not select leanVM's hashing implementation. Our SSE2 and
SSE4.2 verification builds additionally use paired SSE2 FORS hashing. leanVM
selects its own scalar, AVX2 or AVX-512 paths from compiler target features.
These are comparisons of complete implementations, not measurements of two
algorithms forced through the same hash implementation.

Inputs and outputs cross `black_box` boundaries. Fixture generation, byte-for-byte
cross-checks, warmup and calibration are outside the timed region. Kernels are
interleaved in a seeded, shuffled order each round; the positive corpus rotates
across iterations and rounds. Every timed batch is retained. Medians and
percentages are computed from unrounded elapsed times divided by the measured
operation counts. A small percentage from one pass does not establish a
repeatable advantage. Confirm small differences across independent passes and
a larger corpus before attributing them to an optimization.

## Presets and cost

| Preset | Scope | Samples per case per pass | Separate passes | Batch target |
| --- | --- | ---: | ---: | ---: |
| rust | All Rust operations, rejection and hash cases, both recovery providers | 40 | 1 | 10 ms |
| publication | Rotating-corpus signature operations and recovery | 500 | 3 | 200 ms |
| comprehensive | Publication scope, individual positive vectors, malformed inputs and all hash cases | 500 | 3 | 200 ms |
| hashes | Representative hash sizes and padding boundaries | 500 | 3 | 100 ms |

The default publication plan collects 1,500 samples per case. Full ISA coverage is
a long run: planning prints a lower bound before any measurements. Warmup,
calibration, corpus validation, compilation, long individual operations and
cooldowns add time. Use target/group/sample overrides deliberately; no timed
sample has been collected merely by creating this setup.

## Commands

From the repository root:

    python benchmarks/run.py plan --profile rust --cpu 2
    python benchmarks/run.py build --profile rust --cpu 2

After setting the intended machine conditions, start measurements explicitly:

    python benchmarks/run.py run --profile rust --cpu 2

A smaller target selection or a different scope must be supplied consistently to
the plan, build and run commands:

    python benchmarks/run.py plan --targets baseline,native --groups macro,reject
    python benchmarks/run.py build --targets baseline,native --groups macro,reject
    python benchmarks/run.py run --targets baseline,native --groups macro,reject

The runner refuses stale binaries and records exact file hashes, including uncommitted source, for
measurement. It validates binary hashes and applies and verifies process
affinity before releasing the child's start gate. Measurements use one logical
processor. CPU group 0 is supported on Windows; Linux uses sched_setaffinity.

Builds and local sessions live under ignored directories. Compilation never
executes signature operations. Discovery describes compiled features without
generating keys or starting timers.

## Work measured

Signature cases include complete key generation and deterministic signing from
a secret seed, wire verification and a separately identified parsed comparison
API. Three positive specification fixtures and eight deterministic additional
cases are checked byte-for-byte against both implementations before sampling in
the publication and comprehensive presets. The rust preset uses the three
specification fixtures without additional cases.
Each sampling round rotates the corpus and shuffles kernel order with a recorded
seed. No key, signature, tree or signature-operation result is reused in place of
the operation being measured.

Negative cases cover final-path mutation, counter mutation, FORS mutation,
incorrect public keys and messages, truncated signatures, trailing bytes and
empty inputs. Names describe the mutation and do not assume where an invalid
encoding fails.

Hash cases cover 0, 32, 44, 64, 68, 80, 84, 93, 135, 136, 137, 432, 1,072 and
4,096 bytes. They include every important scheme input size and rate-boundary
cases. Scalar/one-shot and vector-batch APIs are distinguished. Batch throughput
is normalized per input and must not be presented as standalone-call latency.

The ecrecover case calls evm2's actual Crypto provider and includes signature
parsing, recovery, serialization and address hashing. Dispatch and transaction
data costs are excluded.

## Diagnosing CPU tuning in tiny-keccak

On the Ryzen 9 8940HX with Rust 1.97.1 / LLVM 22.1.6, automatic SLP
vectorization introduces expensive lane shuffles in tiny-keccak, including
AVX2 verification and AVX-512 single-state hashing. The controlled permutation probe reproduced the
slowdown; disabling SLP removed it. Disabling loop vectorization, lowering only
the dependency's optimization level, and disabling SLP only for that dependency
did not fix the final Thin LTO binary.

The runner automatically disables SLP in tiny-keccak AVX2, AVX-512 and native
builds when the host supports AVX2. The setting covers all compiled crates and Thin LTO.
It preserves target CPU features and hand-written SIMD paths. It is a compiler
setting for the final application build; dependency profile settings alone are
insufficient. It can affect other generated code, so its flags and results are
recorded separately from the default build.

Build and run the focused comparison with the same machine conditions:

    python benchmarks/run.py build --profile quick --targets native --hashing tiny --recovery libsecp256k1 --unmodified-tiny
    python benchmarks/run.py build --profile quick --targets native --hashing tiny --recovery libsecp256k1 --disable-slp
    python benchmarks/run.py run --profile quick --targets native --hashing tiny --recovery libsecp256k1 --unmodified-tiny
    python benchmarks/run.py run --profile quick --targets native --hashing tiny --recovery libsecp256k1 --disable-slp

The fixed builds have a distinct binary ID ending in `-no-slp`.
`--unmodified-tiny` is an explicit diagnostic opt-out; `--disable-slp` applies
the flag to all selected backends. Both the job and
build metadata retain `-C no-vectorize-slp`; existing measurements keep their
original flags. Select other CPU settings with `--targets` and hashing/recovery
implementations with `--hashing` and `--recovery`.

The isolated `keccak_codegen` benchmark measures the permutation and fixed hash
sizes using the locked tiny-keccak dependency. Its known empty-input digest is
checked before timing. The investigation also checks all reported digests
against the shared corpus. Pass `--run` explicitly to measure:

    cargo +1.97.1 bench --manifest-path benchmarks/evm2/Cargo.toml --bench keccak_codegen --features tiny-keccak -- --run

The full-signature before/after sessions for this investigation used 30 samples,
one pass and identical three-fixture inputs on CPU 2, with boost disabled under
the current power policy. They are separate from the earlier boost-enabled
README measurements. Both complete raw sessions, their compiler commands,
feature metadata and clock logs remain local under benchmarks/results.

## Raw data and interruptions

Sampling writes complete raw records: elapsed nanoseconds, calibrated iteration
counts, normalized work-item counts, sample indices and within-round positions.
Checkpoint files are marked running. A final file is marked complete only after
all requested samples have been collected. No outliers are silently removed.

A session journal records successful tasks and their hashes. Interrupted tasks
retain their partial data and logs; resume skips only verified completed tasks.
Resume requires the same source and sampling plan:

    python benchmarks/run.py run --profile rust --cpu 2 --session PATH --resume

Raw sessions remain local under benchmarks/results. The corpus export contains
public deterministic fixtures, hash answers and exact recovery wire bytes for
matching independent runners.

## Machine conditions

Capture includes CPU model, physical/logical core counts, cache sizes, memory, AC power status,
OS/build, BIOS version, active power scheme and all processor policies, including hidden boost settings. Windows
telemetry records OS-reported processor frequency/performance, utilization,
process CPU time and working set while the child runs.

WMI and performance-counter frequencies may be nominal, estimated or stale.
They are not hardware effective clocks or temperature measurements. If hardware
sensor logs are collected separately, retain them alongside the session and
identify the sensor/tool in the eventual write-up. Record boost/overclock
settings, power source and ambient conditions as run notes when relevant.
The runner must not invent a sustained clock from a marketing boost frequency.

## Analysis and README preparation

After a complete run:

    python benchmarks/run.py report --session PATH

This writes a local summary and README-benchmarks.md inside the ignored session
directory. It does not edit README.md. By default the draft contains this crate's
results and the pinned comparison. Use `--no-reference` to omit comparison columns.
The draft contains CPU, compiler and sample count followed by labeled
signature and ecrecover tables. Raw policies, affinity, timestamps, clock logs,
confidence intervals and secondary rejection/hash cases remain in the JSON files.

Report median, p05/p95/p99 batch averages, variation between passes, and a 95%
block-bootstrap interval for the median. These are distributions of batch
averages, not individual-operation tail latencies. Retain all raw samples and
report noisy runs rather than picking the best repetition.

Before publishing a table, identify the CPU, observed clock source, power/boost
settings, OS, compiler/LLVM, target flags, hashing/recovery features, fixture
scope, sample count, number of passes and source revisions. Results from one
machine or a CPU-time ratio do not establish consensus gas pricing.

## Published measurements

[measurements.json](measurements.json) contains the 40 recorded batch times per
case behind every README timing, plus the parsed-verification diagnostics.
The README reports one pass over the three positive specification fixtures.
This is a small conformance corpus, not a representative distribution of signing
times over arbitrary keys and messages. Signing's counter search is input-dependent.

The data records iteration and work-item denominators, exact compiler flags,
binary hashes, source-file hashes, dependency revisions and compiled hash paths.
The elapsed-time array preserves sampling order; no outliers are removed. Local
paths, machine policy logs and unrelated session details are excluded. Recompute
the summaries and README draft without compiling or timing any code:

    python benchmarks/run.py report --measurements benchmarks/measurements.json

The generated files are written to the ignored `benchmarks/results/published`
directory. Confidence intervals describe batch averages within this recorded
pass; they do not measure between-run or between-machine variation.

Signature timings and libsecp256k1 recovery use the dedicated operation-only run.
k256 recovery uses its isolated recovery run. Both AVX2 tiny-keccak configurations
were remeasured after applying `no-vectorize-slp`; the complete configurations
replace their earlier measurements. No individual samples or fastest cases were
selected. The AVX2, AVX-512 and native tiny-keccak rows use the compiler fix;
the other rows retain their original compiler settings.

## Setup validation

The synthetic analysis checks do not execute benchmark binaries:

    python -m unittest discover -s benchmarks/suite -p test_setup.py

Type checking likewise starts no measurements:

    cargo +1.97.1 check --locked --manifest-path benchmarks/evm2/Cargo.toml --bench matrix --all-features

On Windows, the builder prefers Git's bundled GNU patch and Perl when available.
Their versions and the assembly build transcript are recorded. Older patch tools
may fail while preparing AVX-512 assembly; dependency sources are not modified.
A cooperating-runner lock prevents simultaneous measurements on the selected CPU.
