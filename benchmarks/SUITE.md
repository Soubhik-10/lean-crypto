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
selection and actual batch widths for FORS, WOTS+C and leanVM.

## Direct public API comparison

The current README compares this crate with the unmodified native Rust
`lean_sphincs` package from leanVM at
[`4937c851eafb9e93bc7436eebe9e6dc8ae4c227a`](https://github.com/leanEthereum/leanVM/tree/4937c851eafb9e93bc7436eebe9e6dc8ae4c227a/crates/lean_sphincs).
The `direct` cases in [matrix.rs](evm2/matrix.rs) time these upstream functions:

```rust
reference_sphincs::key_gen(&seed.0);
reference_sphincs::sign(&seed.0, &message.0);
reference_sphincs::verify(&parsed_key, &message.0, &parsed_signature);
```

The corresponding calls are `lean_sphincs::key_gen`, `lean_sphincs::sign` and
`lean_sphincs::verify`. Both library implementations are unchanged. The harness
selects inputs and passes arguments/results through `black_box`.

| Operation | lean-sphincs | Unmodified leanVM |
| --- | --- | --- |
| Verification | Borrows the encoded 7,740-byte signature and Alloy public key | Borrows its native public-key and signature objects, parsed before timing |
| Signing | Returns its native `Result<Signature, SignError>` | Returns its native `LeanSphincsSignature`; no timed `to_bytes()` call |
| Key generation | Returns its native `B256` public key | Returns its native `LeanSphincsPublicKey`; no timed `to_bytes()` call |

The verification input representations therefore differ. These are native API
timings, not a claim that both receive identical byte-format inputs. Seed/message
pairs and scheme parameters are identical. Fixture generation, parsing for
leanVM verification, and byte-for-byte correctness checks occur before timing.
Signing and key generation recompute from the seed on every timed call; no
previous result or persistent tree cache substitutes for either operation.

leanVM uses its own hash implementation. All four confirmed signature builds
enable its AVX-512 single-state permutation. Its signature APIs do not call the
separate batched hashing API. RustCrypto, tiny-keccak and asm-keccak select this
crate's Alloy backend, not leanVM's. Both libraries share compiler, target and
LTO flags within each measured binary. `no-vectorize-slp` leaves explicit SIMD enabled.

The `raw` preset measures six direct calls over the same 11-input corpus, with
44 samples per pass and three passes. Sample offsets rotate across the corpus;
44 is a multiple of 11, ensuring equal input weighting over each pass. Kernel
order is shuffled each round. All samples are retained. Add
`--groups direct,ecrecover` to include the direct evm2 recovery call. The k256
provider gets a recovery-only build. Recovery uses one fixed valid ECDSA input.

A fresh screening sweep measured eleven signature builds: AVX2, AVX-512 and
native targets with RustCrypto, tiny-keccak and asm-keccak, plus native RustCrypto
and asm-keccak with SLP disabled. A separate six-build sweep measured k256 using
the same three targets with RustCrypto and asm-keccak. Every screening case has
11 samples. The complete screening median selects one candidate per signature
operation/implementation and recovery provider; their union contains five builds.

Initial confirmation measures those five builds in three passes of 44 fresh samples.
Four include both signature libraries and libsecp256k1 recovery; the fifth
measures k256 recovery. Any additional recovery winners from the later full
matrix are confirmed with the same three-pass scope. Screening and full-matrix
samples are excluded from confirmation medians. Headline values select
the lowest complete 132-sample median for each implementation and operation,
not individual samples or the fastest pass. Small differences between builds
are not attributed to a hashing-backend change inside leanVM. These results do
not establish a universal performance limit.

Raw builds omit `experimental-simd`; the builder checks that the compiled
`experimental_adapter` marker is false. Only the native signature API calls and
evm2's provider call are timed. No local experimental implementation, added
signature decoding, output serialization, VM execution or proof generation is timed.

Reproduce the confirmation candidates with these build/run pairs:

    python benchmarks/run.py build --profile raw --targets native --hashing portable,assembly --recovery libsecp256k1 --groups direct,ecrecover --disable-slp
    python benchmarks/run.py run --profile raw --targets native --hashing portable,assembly --recovery libsecp256k1 --groups direct,ecrecover --disable-slp
    python benchmarks/run.py build --profile raw --targets native --hashing assembly --recovery libsecp256k1 --groups direct,ecrecover
    python benchmarks/run.py run --profile raw --targets native --hashing assembly --recovery libsecp256k1 --groups direct,ecrecover
    python benchmarks/run.py build --profile raw --targets v4 --hashing assembly --recovery libsecp256k1 --groups direct,ecrecover
    python benchmarks/run.py run --profile raw --targets v4 --hashing assembly --recovery libsecp256k1 --groups direct,ecrecover
    python benchmarks/run.py build --profile raw --targets v3 --hashing assembly --recovery k256 --groups ecrecover
    python benchmarks/run.py run --profile raw --targets v3 --hashing assembly --recovery k256 --groups ecrecover

The recorded confirmation session shuffles the five binaries each pass. The
commands above reproduce the same candidates and sampling scope in separate
sessions. Exact compiler flags, selected screening winners and every raw sample
are recorded in [raw-api-measurements.json](raw-api-measurements.json).

## Earlier wire-format comparison

The earlier wire-format tables compare APIs using identical leanSPHINCS parameters,
secret seeds, messages and expected wire encodings. Verification starts with a
32-byte public key and a 7,740-byte signature. It includes leanVM's decoding into
its internal representation and this crate's in-place reads. Signing includes
signature serialization on both sides; key generation returns encoded public
keys on both sides. The separately measured parsed-verification diagnostic is
excluded from the main tables. No VM execution or proof generation is measured.

The [format bridges](evm2/reference.rs) call the original upstream functions and
add only decoding/serialization to match the encoded interface. They do not
replace or optimize its cryptographic algorithms. Those earlier timings remain
valid for that boundary; the current raw API timings use the different native
boundary described above.

Both implementations are compiled into the same binary with the same target,
optimization and LTO settings. Any `no-vectorize-slp` setting applies to both.
The reference implementation is an unmodified pinned Git dependency. The
RustCrypto, tiny-keccak and asm-keccak labels select this crate's Alloy Keccak
implementation; they do not select leanVM's hashing implementation. Verification
uses two-lane FORS hashing on SSE2 and four-lane FORS and WOTS+C hashing on AVX2.
leanVM selects its own scalar, AVX2 or AVX-512 paths from compiler target features.
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
| raw | Direct unmodified public APIs; 11 positive inputs, experimental code excluded | 44 | 3 | 10 ms |
| rust | All Rust operations, rejection and hash cases, both recovery providers | 40 | 1 | 10 ms |
| comparison | Native APIs, unmodified dependency and local SIMD batching adapter; 11 positive inputs | 44 | 3 | 10 ms |
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

## Experimental SIMD comparison

The `batched` group measures the [local adapter](evm2/batched/mod.rs), separately
from the unmodified leanVM API. It uses leanVM's public address, framing,
parameter, decoding and hashing APIs. Its new scheduling code batches independent
FORS openings, WOTS chains, encoding-counter candidates and Merkle parent hashes
through leanVM's `hash_many`. This changes which independent hashes execute
together, not the signature format. Counter search still selects the least
admissible counter. Partial SIMD groups use the dependency's scalar remainder.

Batching occurs inside one key-generation, signing or verification call. The
results are single-operation latency, not throughput obtained by timing multiple
signatures together. Key generation and signing recompute from the seed, and
signing builds and reuses its top tree only within that call. The adapter is
experimental benchmark code, not an upstream leanVM implementation or a new
production backend in this crate.

The adapter assembles encoded signatures directly, uses leanVM's public decoders
for WOTS/hypertree fields and reads FORS authentication paths from the encoded
input. These data-flow choices are part of the adapter; this is not a claim that
turning on a Cargo feature gives unmodified leanVM these results.

The `comparison` preset checks the three positive specification fixtures and
eight additional deterministic key/message pairs against all implementations
before timing. Standalone differential checks also cover generated inputs,
mutations, incorrect keys/messages and malformed lengths under scalar, AVX2 and
AVX-512 builds:

    cargo test --locked --profile bench --manifest-path benchmarks/evm2/Cargo.toml --test batched

The sample count is a multiple of the corpus size. With the rotating input
offset, every input receives equal weight over each complete pass even when
implementations calibrate different batch iteration counts.

Reproduce the two confirmed configurations with:

    python benchmarks/run.py build --profile comparison --targets native --hashing portable,assembly --recovery libsecp256k1 --disable-slp
    python benchmarks/run.py run --profile comparison --targets native --hashing portable,assembly --recovery libsecp256k1 --disable-slp

For a best-configuration comparison, first run a short sweep, retaining every
configuration's samples. Select candidates using complete operation medians,
then measure those candidates in a separate three-pass run. Report the build
configuration for each candidate. Tuning samples must not be mixed with the
confirmation samples, and "best measured" must not be presented as a proven
performance limit.

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

The current README uses [raw-api-measurements.json](raw-api-measurements.json):
6 confirmation builds, 44 samples per case per pass and three passes. It
contains all 3,960 batch timings, per-pass operation counts, exact compiler
flags, binary/source hashes and dependency revisions. The separate
[screening dataset](raw-api-screening.json) retains all seventeen candidate builds.
[RAW_RESULTS.md](RAW_RESULTS.md) shows every matched confirmation build. The
headline selects the lowest complete median per implementation and operation;
it does not select individual samples or the fastest pass.

The [measured source snapshot](https://github.com/Soubhik-10/lean-sphincs/tree/ffd83f95d9d5fa28e27115c976a12a1f765e157b)
matches every recorded source-file hash. Both signature libraries are unmodified,
and the experimental implementation is excluded from the measured binaries.
Recompute summaries and the signature tables from raw data without timing code:

    python benchmarks/run.py report --measurements benchmarks/raw-api-measurements.json

The README also includes the [full raw API matrix](raw-api-matrix.json):
all five CPU targets, three Alloy Keccak backends and two evm2 recovery providers.
These 30 configurations contain 5,280 fresh batch timings: 44 samples per case in
one pass. Signature cases use the same 11-input corpus; recovery uses the same
fixed ECDSA input. Their samples remain separate from three-pass confirmation.
Reproduce the matrix with:

    python benchmarks/run.py build --profile raw --targets baseline,v2,v3,v4,native --hashing portable,tiny,assembly --recovery libsecp256k1,k256 --groups direct,ecrecover
    python benchmarks/run.py run --profile raw --targets baseline,v2,v3,v4,native --hashing portable,tiny,assembly --recovery libsecp256k1,k256 --groups direct,ecrecover --passes 1

The earlier local SIMD experiment has two separate datasets:

- [simd-sweep.json](simd-sweep.json): all 25 CPU/backend/compiler configurations,
  11 samples per case and one pass. This selects candidates.
- [simd-confirmation.json](simd-confirmation.json): both selected native-CPU builds,
  44 samples per case per pass and three passes, giving 132 samples per case.
  This supplies the archived local-prototype comparison, not the current README.

Both use the same 11 key/message pairs: three specification fixtures and eight
deterministic generated cases. The archived experiment selects the lowest complete confirmation
median for each implementation and operation; it does not select individual
samples or the fastest pass. The selection and exact candidate binaries are
recorded in the confirmation data. Small differences between the two builds are
not claimed as statistically significant. Full matched-build tables show both.

The [experimental source snapshot](https://github.com/Soubhik-10/lean-sphincs/tree/75268418b47f99042c9176a0e8efaa080138a454)
was verified byte-for-byte against every recorded source-file hash. The captured
base revision predates this snapshot because measurement occurred with
uncommitted changes. `measurement_source_commit` identifies the complete measured
tree; `source_revision` records that earlier base. The pinned upstream dependency
is unmodified in both the stock and locally adapted comparison.

The data records iteration and work-item denominators, exact compiler flags,
binary hashes, source-file hashes, dependency revisions and compiled hash paths.
The elapsed-time array preserves sampling order; no outliers are removed. Local
paths, machine policy logs and unrelated session details are excluded. Recompute
the summaries and README draft without compiling or timing any code:

    python benchmarks/run.py report --measurements benchmarks/simd-confirmation.json
    python benchmarks/run.py report --measurements benchmarks/simd-sweep.json

The generated files are written to the ignored `benchmarks/results/published`
directory. Confidence intervals describe the recorded batch averages across
these passes; they do not establish performance across machines or arbitrary
key/message distributions. Signing's counter search is input-dependent.

[measurements.json](measurements.json) retains the earlier 40-sample, single-pass
matrix over three specification fixtures, including the separate ecrecover
measurements still shown in the README. Its signature timings are historical,
not the current SIMD comparison. Its entire AVX2 tiny-keccak configurations were
remeasured with the compiler fix; no individual timed samples were replaced.

## Setup validation

The synthetic analysis checks do not execute benchmark binaries:

    python -m unittest discover -s benchmarks/suite -p test_setup.py

Type checking likewise starts no measurements:

    cargo +1.97.1 check --locked --manifest-path benchmarks/evm2/Cargo.toml --bench matrix --all-features

On Windows, the builder prefers Git's bundled GNU patch and Perl when available.
Their versions and the assembly build transcript are recorded. Older patch tools
may fail while preparing AVX-512 assembly; dependency sources are not modified.
A cooperating-runner lock prevents simultaneous measurements on the selected CPU.
