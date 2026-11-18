# Linux benchmark suite

The benchmark kernels are Rust. Bash orchestrates planning, compilation, CPU
allocation and execution; `jq` validates JSON; `awk` computes statistics.
Linux and WSL are supported.

## Requirements

Use Bash 4.3 or newer, jq 1.6 or newer, awk, Git, GNU coreutils, util-linux
(`taskset`, `flock`, `setsid`) and the Rust 1.97.1 toolchain. Assembly builds also
need a working C toolchain, Perl and patch. Install build tools through the Linux
distribution's package manager; install Rust with rustup.

Run commands from the repository root. Paths containing spaces are supported.
The scripts do not change power settings or CPU frequency policy.

## Native signature and evm2 matrix

Planning probes CPU/OS instruction support without generating keys, signatures
or proofs. Unsupported ISA targets are listed in `skipped`. On ARM, select
`native`; x86-specific targets are skipped. Choose a logical CPU inside the
current process allocation with `--cpu`; the default is the first allowed CPU.

```sh
bash benchmarks/run.sh plan --profile raw --groups direct,ecrecover
bash benchmarks/run.sh build --profile raw --groups direct,ecrecover
bash benchmarks/run.sh run --profile raw --groups direct,ecrecover
```

`build` only compiles and inspects `--describe`. Only `run` starts measurements.
The Rust binary checks shared fixtures before sampling. Both libraries' public
keys and complete deterministic signatures must agree before timing.

The matrix covers five x86 compiler targets, three Alloy hashing backends and
two evm2 ECDSA recovery providers. The alternative k256 provider gets a
recovery-only job, since changing the recovery provider does not change the
signature algorithms. `raw` is the default profile and excludes local adapters.

| Selection | Choices |
| --- | --- |
| `--targets` | `baseline`, `v2`, `v3`, `v4`, `native` |
| `--hashing` | `portable` (RustCrypto), `tiny` (tiny-keccak), `assembly` (asm-keccak) |
| `--recovery` | `libsecp256k1`, `k256` |
| `--groups` | `direct`, `ecrecover`, `macro`, `reject`, `hash`, `batched` |

The target identifiers map to `x86-64`, `x86-64-v2`, `x86-64-v3`, `x86-64-v4`
and `native` compiler flags. README labels use SSE2, SSE4.2, AVX2, AVX-512 and
native. The complete x86 matrix has 30 configurations and 120 operation/build
pairs when selecting `direct,ecrecover`.

| Profile | Samples per pass | Passes | Scope |
| --- | ---: | ---: | --- |
| `raw` | 44 | 3 | Six native API calls over 11 shared inputs |
| `rust` | 40 | 1 | Encoded APIs, rejection and isolated hashing |
| `quick` | 30 | 1 | Encoded APIs over three specification fixtures |
| `publication` | 500 | 3 | Longer encoded-API campaign |
| `comprehensive` | 500 | 3 | Per-fixture APIs, rejection and hashing |
| `hashes` | 500 | 3 | Isolated hashing |
| `comparison` | 44 | 3 | Historical local batching experiment, explicitly selected |

Override `--samples`, `--passes`, `--sample-ms`, `--groups` and
`--cooldown-seconds` explicitly. Direct/batched sample counts must be a multiple
of the shared corpus size. The reported duration is a lower bound; it excludes
fixture generation, calibration and operations longer than the requested batch.

A focused build/run pair is:

```sh
bash benchmarks/run.sh build --profile raw --targets native --hashing portable,assembly --recovery libsecp256k1 --groups direct,ecrecover
bash benchmarks/run.sh run --profile raw --targets native --hashing portable,assembly --recovery libsecp256k1 --groups direct,ecrecover --session benchmarks/results/my-run
```

Builds are stored under ignored `benchmarks/build/linux`, separately from older
Windows artifacts. Each configuration preserves its own executable and hash.
The index records exact Rust flags, compiler, resolved Cargo features, dependency
sources and the C build environment. Source hashes and binary hashes must match
before execution. Process-global Keccak caching is rejected.

## Direct public API comparison

The `direct` kernels in [matrix.rs](evm2/matrix.rs) call this library and upstream
leanVM without a local batching adapter:

```rust
reference_sphincs::key_gen(&seed.0);
reference_sphincs::sign(&seed.0, &message.0);
reference_sphincs::verify(&parsed_key, &message.0, &parsed_signature);
```

Our corresponding calls are `lean_sphincs::key_gen`, `lean_sphincs::sign` and
`lean_sphincs::verify`. Arguments and results pass through `black_box`.
Verification uses parsed native inputs for leanVM and encoded bytes for this
crate. Signing and key generation return native values and recompute from the
seed on each call, without extra timed serialization.

The hash labels select Alloy hashing. leanVM uses its own CPU-selected code;
its signature and Keccak packages have no optional Cargo features. Raw builds
must report `experimental_adapter: false`. The separate `batched` group enables
the local experimental adapter and is clearly distinguished in generated reports.
It is not stock leanVM performance.

See [BENCHMARK_SETUP.md](BENCHMARK_SETUP.md) for exact published revisions,
features, API boundaries, and the evm2 recovery-provider definitions.

## tiny-keccak compiler workaround

Affected tiny-keccak AVX2, AVX-512 and native builds automatically apply
`-C no-vectorize-slp` through the complete Thin LTO build. This avoids the
reproduced LLVM 22 code-generation regression while retaining explicit SIMD.
The configuration ID ends in `-no-slp`, and the exact flag is recorded.

`--disable-slp` applies the same flag to every selected backend.
`--unmodified-tiny` explicitly disables the automatic workaround for diagnosis.
Flags apply to both Rust libraries within a binary. Dependency-only profile
changes did not fix the original final-binary regression.

## Execution, interruption and resume

`taskset` applies affinity before the benchmark process starts. Native binaries
also wait for an input start gate. `flock` prevents cooperating runners from
measuring on the same CPUs. An interrupted or timed-out command has its process
group terminated, including recursive children. `--timeout SECONDS` optionally
bounds each native binary; the default has no timeout.

The session journal records successful tasks, raw-file hashes and the shared
corpus hash. Each task retains every elapsed time, iteration count, work-item
count, input offset and within-round position. No outliers are removed.
Incomplete files cannot be reported as complete. Resume validates sources,
compiler, binary hashes, machine conditions, completed samples and corpus:

```sh
bash benchmarks/run.sh run --profile raw --groups direct,ecrecover --session benchmarks/results/my-run --resume
```

Use the same options as the original session. Completed tasks are not rerun.
Partial attempts are archived within the session before retrying their names.

## Reports

Reporting never compiles or executes a benchmark:

```sh
bash benchmarks/run.sh report --session benchmarks/results/my-run
bash benchmarks/run.sh report --measurements benchmarks/raw-api-measurements.json
bash benchmarks/prover/run.sh report --measurements benchmarks/proving-measurements.json
```

Generated `summary.json`, `summary.csv` and `README-benchmarks.md` stay under the
ignored results directory. Session reports also export normalized measurements.
The root README and committed measurements are never overwritten automatically.
`--no-reference` omits comparison columns from the native Markdown draft.

Statistics include complete medians, means, standard deviations, p05/p95/p99,
per-pass medians and a 95% circular block-bootstrap interval. Blocks of ten
samples are drawn within each pass; every original sample is retained. The
bootstrap defaults to 2,000 resamples and uses a fixed seed; `--bootstrap`
selects 100 through 100,000 resamples. Bootstrap draws are reproducible with the
same awk implementation. These distributions describe batch averages, not
individual-operation tail latencies or performance across machines.

Published schema versions 1 and 2 are accepted. Missing/duplicate passes,
missing samples, invalid denominators and duplicate operation/build records are
rejected. Percent faster means `(baseline time / compared time - 1) * 100%`,
calculated before formatting; negative values remain visible.

## Stock leanVM proving

[The prover runner](prover/README.md) compares unmodified upstream CLIs using
`--prover stable` and `--prover experimental`. Those are runtime options.
Its quick plan covers both pinned revisions, three workloads, one worker and up
to sixteen available physical cores. It includes leaf and recursive aggregation.
Only `run --execute` generates signatures or proofs, including cache preparation.

## Published measurements

The [current native confirmation](raw-api-measurements.json) retains 4,884 batch
timings from seven builds; the [full matrix](raw-api-matrix.json) retains 5,280.
[RAW_RESULTS.md](RAW_RESULTS.md) lists every matched row and winning build.
[proving-measurements.json](proving-measurements.json) retains all 24 CLI jobs and
120 proving passes; [PROVING_RESULTS.md](PROVING_RESULTS.md) includes slower rows,
verification time, proof size and parent-process peak RSS.

These published native measurements used Windows MSVC; the published proving
measurements used Linux GNU under WSL2. The later shell port changes orchestration,
not those measurements. Fresh Linux native runs use the GNU toolchain and form a
separate campaign. Historical source hashes remain unchanged in the raw JSON;
the recorded Git snapshots retain the older orchestration for audit.

[raw-api-screening.json](raw-api-screening.json), [measurements.json](measurements.json),
[simd-sweep.json](simd-sweep.json) and [simd-confirmation.json](simd-confirmation.json)
are historical datasets with their own source revisions and boundaries. They are
not pooled into the current confirmation. The local SIMD experiment is distinct
from the unmodified raw API comparison.

## Setup validation

```sh
bash benchmarks/suite/test_setup.sh
```

The shell tests use synthetic executable/report fixtures. They cover CPU/ISA
selection, SLP controls, timing denominators, report completeness, bootstrap
statistics, affinity, timeout cleanup, session reporting and no-op resume.
Changed source, binary or sample hashes must be rejected. No cryptographic
benchmarks or upstream proofs are run by this test suite. Linux CI also checks
shell syntax and compiles the CPU probe.
