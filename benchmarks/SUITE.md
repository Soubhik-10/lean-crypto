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

## Compare ours, leanVM and ecrecover

Run these from the existing repository. The focused entrypoint builds, measures
and reports automatically. Linux/WSL native results form a new campaign; the
published Windows measurements retain their original setup.

```sh
# Inspect jobs without building or measuring.
bash benchmarks/compare.sh native plan

# Our key generation/signing/verification, stock leanVM APIs and real evm2 recovery.
bash benchmarks/compare.sh native --session benchmarks/results/native-comparison

# Add RustCrypto/assembly hashing and C-backed/k256 recovery controls.
bash benchmarks/compare.sh backends --session benchmarks/results/backend-comparison

# Isolate the hashing kernels; no signature/proof timings in the results.
bash benchmarks/compare.sh hashes --session benchmarks/results/hash-comparison
```

The native/backends presets use 11 shared PQ fixtures, 44 batch samples per
process, three fresh processes per configuration, 300 ms warmup and 20 ms batch
targets. Kernels are interleaved in randomized order. The hashes preset uses
30 samples and 500 ms warmup. Setup validates the fixtures before timing.
The `direct` group calls unmodified native APIs; the local experimental
batching adapter is excluded. Each k256 job measures recovery only; matching
PQ measurements are supplied by the same-hashing C-provider configuration.

The runner chooses the first allowed logical CPU unless `--cpu` is supplied.
Set `--cc` to an installed C compiler executable to make compiler comparisons
explicit. Each preset/compiler gets a separate build directory; source and
binary fingerprints guard runs and resume.

```sh
# Select CPU 8 only if it is in this process's allowed allocation.
bash benchmarks/compare.sh native --cpu 8 --cc clang \
  --session benchmarks/results/native-clang

# Override the workload length; direct sample counts must be multiples of 11.
bash benchmarks/compare.sh native --samples 88 --passes 3 --sample-ms 50 \
  --session benchmarks/results/native-long

# Build without starting measurements.
bash benchmarks/compare.sh native build --cc clang

# Resume skips rebuilding and validates the existing session/binaries.
bash benchmarks/compare.sh native --session benchmarks/results/native-comparison --resume

# Regenerate reports without executing any benchmark.
bash benchmarks/compare.sh native report --session benchmarks/results/native-comparison
```

Keep the same preset, compiler and workload overrides when resuming. A fresh
run requires a new session path. Output includes `README-benchmarks.md`,
`summary.json`, `summary.csv`, normalized `measurements.json`, complete raw
reports and setup fingerprints. No result is written into the repository README.

## Aggregate verifier

The verifier preset uses the same CPU-allocation, process-launch and machine/source
fingerprint helpers. It compares the independent `lean-verifier` with its pinned
native leanVM verifier on the same leaf and recursive aggregate proofs, including
deferred evaluation, both with and without decoding. All setup and proving are
outside the timer. Default and assembly streaming hashes are separate builds.

```sh
bash benchmarks/compare.sh verifier plan
bash benchmarks/compare.sh verifier build
bash benchmarks/compare.sh verifier --cpu 8 --session benchmarks/results/verifier-run
bash benchmarks/compare.sh verifier report --session benchmarks/results/verifier-run

# Optional longer workload; three fresh processes per hashing build remain the default.
bash benchmarks/compare.sh verifier --cpu 8 --rounds 9 --iterations 60 \
  --session benchmarks/results/verifier-long
```

The default is three fresh processes, five sampling rounds each and 30 calls
per round. Calls alternate implementation order, and hashing-build order rotates
between processes. Reports use medians of per-round means and paired round ratios;
every individual timing is retained. The leaf contains two leanSPHINCS signatures,
and its recursive parent retains one claim; both use log-inverse-rate 1. Verification
alone assumes decoded proofs; decoding + verification includes unpruning and its
hashes. Program preparation and reference proving are excluded from both.

Select `--hashing portable` or `--hashing assembly` for one build. `--target-cpu`
defaults to `native`; CPU selection must lie inside the current allocation.
A new run requires a fresh `--session`. Metadata records the exact source and
binary fingerprints, dependency features, Rust/C compiler, flags, CPU and sampling
settings. The report rejects missing/duplicate processes and incomplete samples.
See the [crate results](../crates/lean-verifier/README.md#validation-and-benchmarks).

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

See [published setup](README.md#setup) for revisions, API boundaries and recovery-provider definitions.

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
bash benchmarks/run.sh report --measurements benchmarks/archive/data/raw-api-measurements.json
bash benchmarks/prover/run.sh report --measurements benchmarks/archive/data/proving-measurements.json
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

[Current Rust results](README.md) link to the retained datasets and setup.
[Historical reports](archive/README.md) contain older native matrices, local
adapter experiments and upstream proving campaigns. The [data index](data/INDEX.md)
lists current evidence without mixing campaigns.

Published native results used Windows MSVC; proving used Linux GNU under WSL2.
The shell runner changes orchestration, not those measurements. New Linux
native runs form a separate campaign. Historical source hashes and recorded
build paths remain unchanged inside the raw files.

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
