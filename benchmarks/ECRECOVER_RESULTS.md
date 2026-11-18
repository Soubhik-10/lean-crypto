# leanSPHINCS versus evm2 ecrecover

Measured 18 November 2026 on an AMD Ryzen 9 8940HX, Windows x86-64 MSVC,
Rust 1.97.1 / LLVM 22.1.6. The benchmark profile uses optimization level 3,
Thin LTO and one codegen unit.

## Fresh upstream leanVM versus evm2 confirmation

This separate campaign measures **upstream leanVM's native verifier**, pinned to
[`6a828ecf`](https://github.com/leanEthereum/leanVM/tree/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b),
against the actual evm2 recovery provider. The same-process lean-sphincs column
is a control from our crate. These are medians of 132 retained batch samples
per operation/configuration, collected in three fresh processes on the AMD
machine above.

| evm2 recovery backend | leanVM verify (µs) | evm2 ecrecover (µs) | leanVM / ecrecover | Ratio × 3,000 gas | Ratio × 2,800 gas | Our verify control (µs) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Clang C/libsecp256k1 | 121.076 | 25.545 | 4.740x | 14219 | 13271 | 37.016 |
| Rust k256 | 119.701 | 50.825 | 2.355x | 7066 | 6595 | 40.970 |

The faster Clang C recovery control gives **4.740x**,
or approximately **14219 gas** at the existing
[3,000-gas precompile anchor](https://eips.ethereum.org/EIPS/eip-1108#specification),
and **13271 gas** at the
[draft 2,800-gas native signature anchor](https://eips.ethereum.org/EIPS/eip-8141).
At the [draft 12,600-gas leanSPHINCS charge](https://github.com/ethereum/EIPs/pull/12616),
the ratio of CPU time per gas to the 2,800-gas recovery reference is
1.0533x. This is a local timing
calibration, not gas consumed by the Rust call or a network-wide pricing verdict.
The measured format has 515 permutations; the proposal's older 492-permutation
pin and the [13,200-gas review suggestion](https://github.com/ethereum/EIPs/pull/12616#pullrequestreview-5920543343)
still need to be distinguished.

Upstream verification uses its own native AVX-512 single-state Keccak path in
both configurations. Disabling Alloy's optional assembly feature in the k256
build does not replace leanVM's hashing backend. The pinned upstream verifier
walks independent [FORS trees](https://github.com/leanEthereum/leanVM/blob/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b/crates/lean_sphincs/src/fors.rs)
and [WOTS chains](https://github.com/leanEthereum/leanVM/blob/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b/crates/lean_sphincs/src/wots.rs)
sequentially. Our native verifier batches independent hashes in four AVX2
lanes. The same-process Clang row measures our verifier as
3.27x faster than upstream on this CPU.

Our Clang-build control has process medians of 37.016, 52.141 and 36.512 µs.
The second process stays slower across all 44 samples; it is not a single
outlier. Its batch calibration chooses 512 iterations instead of 1,024.
The cause is not isolated by this campaign. All samples remain included and
the pooled speedup does not describe every process. The upstream and recovery
kernels in that process remain close to their other passes, as shown below.

The pure-Rust recovery baseline takes longer and therefore gives a smaller
ratio. It does not reduce the upstream verifier's work. Use the Clang C row
when comparing against the faster measured recovery backend.

| Recovery backend | Pass | leanVM verify (µs) | evm2 ecrecover (µs) | Ratio | Our verify control (µs) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Clang C/libsecp256k1 | 1 | 121.929 | 26.076 | 4.676x | 37.016 |
| Clang C/libsecp256k1 | 2 | 121.076 | 25.521 | 4.744x | 52.141 |
| Clang C/libsecp256k1 | 3 | 119.785 | 25.517 | 4.694x | 36.512 |
| Rust k256 | 1 | 119.563 | 50.999 | 2.344x | 41.518 |
| Rust k256 | 2 | 122.498 | 50.773 | 2.413x | 40.904 |
| Rust k256 | 3 | 118.409 | 50.775 | 2.332x | 40.560 |

| Recovery backend | Operation | p05 (µs) | Median (µs) | p95 (µs) |
| --- | --- | ---: | ---: | ---: |
| Clang C/libsecp256k1 | leanVM verify | 119.514 | 121.076 | 122.948 |
| Clang C/libsecp256k1 | evm2 ecrecover | 25.452 | 25.545 | 26.197 |
| Clang C/libsecp256k1 | Our verify control | 36.420 | 37.016 | 52.540 |
| Rust k256 | leanVM verify | 117.179 | 119.701 | 122.879 |
| Rust k256 | evm2 ecrecover | 50.612 | 50.825 | 51.514 |
| Rust k256 | Our verify control | 40.432 | 40.970 | 41.833 |

Each process runs 44 randomized rounds, with 300 ms warmup per kernel and
adaptive batches targeting at least 20 ms. Configuration order is Clang/k256,
k256/Clang, Clang/k256. Affinity (CPU 8) and above-normal priority are checked
before releasing the start handshake. AC power remains connected. The Balanced
power policy is unchanged; SMT sibling 9 is not reserved, and temperature and
clock frequency are not fixed or measured. Percentiles describe batch-average
times, not individual-call latency or confidence intervals.

The binaries are the already audited native builds, reused after verifying
executable and implementation/harness source hashes. Both are Rust 1.97.1,
MSVC ABI, optimization level 3, native CPU features, Thin LTO and one codegen
unit. The C backend uses Clang-cl 21.1.8 with secp256k1 0.33.1 / sys 0.14.1;
the alternative provider uses k256 0.14.0. Dependency pins remain the revisions
listed below. Run the existing matrix with `--sample-ms 20 --groups direct,ecrecover`
using the reproduction procedure below for this campaign's batch settings.

All eleven shared PQ fixtures are checked for byte-identical keys/signatures
before timing. leanVM inputs are parsed before timing, while our API receives
signature bytes. Recovery includes parsing, public-key recovery, serialization
and address hashing, with provider initialization outside timing. This campaign
uses the existing fixed ECDSA input; the 32-input audit below checks its
representativeness. No EVM execution, signature-data charges or aggregation
proof work is included. All seven existing direct/recovery kernels run in
each process; the full data also retains signing and key-generation samples.

[All six reports, 1,848 samples, corpus, setup, build/source hashes and launch metadata](leanvm-ecrecover-2026-11-18.json).

The [parameter and optimization audit](OPTIMIZATION_AUDIT.md) compares every
logical hash input and isolates batching and hash-backend effects in fresh runs.

## Backend and compiler audit

The earlier near-equality result is specific to the MSVC C build. Rebuilding
the same libsecp256k1 dependency with Clang changes ecrecover substantially,
while lean-sphincs verification stays close to its earlier time:

| Timed Rust configuration | lean-sphincs verify (µs) | evm2 ecrecover (µs) | Verify / ecrecover |
| --- | ---: | ---: | ---: |
| Assembly Keccak + MSVC C/libsecp256k1 | 36.734 | 38.387 | 0.957x |
| Assembly Keccak + Clang C/libsecp256k1 | 36.843 | 25.634 | 1.437x |
| RustCrypto Keccak + Rust k256 | 40.663 | 50.646 | 0.803x |

These audit rows use 32 deterministic ECDSA signatures and eleven leanSPHINCS
fixtures. Each row pools all 132 samples from three fresh processes. Processes
are pinned to CPU 8 at above-normal priority, warm each kernel for 250 ms,
calibrate batches to at least 20 ms and randomize operation order in 44 rounds.
Every sample is retained. Clock frequency and temperature are not fixed.
Compiler configurations run in consecutive blocks; the unchanged Rust kernels
provide contemporaneous controls for the compiler comparison.

The baseline is real native code. evm2's default recovery path calls the Rust
`secp256k1` wrapper around Bitcoin's C libsecp256k1. The checked build uses
Microsoft C 19.44.35222 with `/O2`; the compiler control uses Clang 21.1.8.
Both have the same Rust target, `x86_64-pc-windows-msvc`, and native Rust flags.
The C compiler is a separate choice from the Rust target ABI.

The pure-Rust row builds evm2 with its `secp256k1` feature disabled and
`asm-keccak` disabled throughout the timed paths. Its actual public provider
selects k256; both measured operations use RustCrypto Keccak. Fixture generation
and separate C microbenchmarks still use libsecp256k1, outside those two timed
operations. It is a comparison of the timed implementations, rather than a
claim that the whole diagnostic binary contains no C.

All 32 ECDSA inputs must recover the same public key/address through the C
and k256 paths before timing. The diagnostic also checks the original fixed
fixture and geth's benchmark fixture. Their timings are close to the 32-input
corpus, so the original fixture does not explain the compiler difference.

| Clang C build component | Median (µs) |
| --- | ---: |
| Recovery with signature already parsed | 25.399 |
| Compact-signature parsing alone | 0.018 |
| Public-key serialization alone | 0.020 |
| Address Keccak alone | 0.170 |

Address hashing and parsing are too small to explain the gap. A fresh context
is not created per timed recovery. Most of the measured time is curve recovery.
The compiler changes the generated native recovery code; a pure-language
implementation is not automatically faster.

Our verifier also processes independent FORS and WOTS hashes in four SIMD lanes
on this native x86 build. The Go PoC processes those paths through its hash-state
API. That implementation difference, along with a different CPU and recovery
backend, prevents transferring the ARM 8.4x ratio to this measurement. We have
not measured this crate on the quoted ARM machine.

With the faster Clang-C control, the local 3,000-gas runtime calibration is
approximately **4312 gas**, rather than the earlier
MSVC-C calibration of about 2,900. Neither number establishes a consensus price.
The faster C recovery backend is a useful production control; choosing the
slower k256 baseline merely to match implementation languages would lower the
ratio without reducing leanSPHINCS verification work.

[All audit samples, compiled features, binary hashes and diagnostic source](ecrecover-backend-audit-2026-11-18.json).
The original campaign below is retained with its original measurements.

## Original MSVC-C campaign

These are medians of all 132 retained samples in each configuration, collected
in three fresh processes. The verifier and recovery provider share a binary,
compiler flags and Alloy address-hashing backend. Smaller ratios mean less CPU
time than ecrecover; 1.0x means the same time.

| Build | lean-sphincs verify (µs) | evm2 ecrecover (µs) | Verify / ecrecover | Ratio × 3,000 gas | Ratio × 2,800 frame gas |
| --- | ---: | ---: | ---: | ---: | ---: |
| native, asm-keccak | 36.711 | 38.354 | 0.957x | 2871 | 2680 |
| native, RustCrypto | 40.822 | 38.361 | 1.064x | 3193 | 2980 |
| SSE2, RustCrypto | 100.695 | 38.539 | 2.613x | 7838 | 7316 |

In this original MSVC-C build, the native assembly verifier takes approximately
the same CPU time as evm2's recovery provider. The native RustCrypto build has the same
four-lane explicit SIMD verification path, without the optional assembly hash
backend. The SSE2 build uses two-lane FORS verification and is included as a
baseline for a binary without AVX2 compiler features.

The native assembly build also measures the unmodified leanVM public APIs with
the same flags and the same eleven seed/message pairs:

| Operation | lean-sphincs | leanVM | leanVM time / lean-sphincs time |
| --- | ---: | ---: | ---: |
| Verification (µs) | 36.71 | 120.64 | 3.29x |
| Signing (ms) | 88.25 | 118.68 | 1.34x |
| Key generation (ms) | 46.34 | 61.49 | 1.33x |

These are matched-build results. They do not select a different fastest build
for each implementation or operation. Older full matrices remain in
[native API results](RAW_RESULTS.md). The separate
[upstream proving comparison](PROVING_RESULTS.md) measures leanVM's provers;
this crate does not implement aggregation.

## What is timed

The existing `matrix` harness calls these public APIs directly:

```rust
lean_sphincs::verify(&public_key, &message, signature.as_slice());
evm2::precompiles::crypto()
    .secp256k1_ecrecover(&ecdsa_signature, recovery_id, &ecdsa_message.0);
```

The provider is obtained before timing. Its measured call includes compact
ECDSA parsing, public-key recovery, uncompressed serialization, Keccak address
hashing and the padded address word. evm2's default libsecp256k1 backend is
enabled. This is the actual evm2 provider, rather than a stand-in signature
verification function. EVM dispatch, transaction decoding and transaction-data
charges are outside these measurements.

lean-sphincs receives encoded signature bytes. leanVM receives parsed public
keys and signatures prepared before timing, which gives leanVM the cheaper
input boundary. Signing and key generation recompute from the seed on each
call. No precomputed signing tree replaces measured work.

## Controls and sampling

- Both libraries' public keys and all signature bytes must agree before timing.
- Previously built release executables are reused only after their hashes and
  the implementation/harness source hashes match the build manifest.
- Verification rotates three positive EthLib fixtures and eight deterministic
  seed/message pairs. Recovery uses one validated ECDSA fixture; this is not a
  survey of every ECDSA input or malicious transaction workload.
- Each process is pinned to logical CPU 8 at above-normal priority. SMT sibling
  9 is not reserved. The Balanced power policy is retained; clock frequency
  and temperature are not fixed or measured.
- Every operation has 300 ms of warmup and adaptive calibration for batches
  targeting at least 10 ms. Inputs and outputs pass through `black_box`.
- Each process runs 44 rounds with randomized operation order. The order of
  the three configurations rotates between passes.
- Fixture setup, correctness checks, warmup, calibration and report writes
  are outside the samples. Every sample and outlier is retained.
- Reported medians pool all 132 samples per operation/configuration. The
  following percentiles describe batch-average throughput, not individual-call
  latency or a confidence interval. Percentiles use the sorted sample at
  `floor((sample_count - 1) * fraction)`.

| Build | Operation | p05 (µs) | Median (µs) | p95 (µs) |
| --- | --- | ---: | ---: | ---: |
| native, asm-keccak | verify | 36.439 | 36.711 | 37.641 |
| native, asm-keccak | ecrecover | 38.197 | 38.354 | 40.108 |
| native, RustCrypto | verify | 40.473 | 40.822 | 41.098 |
| native, RustCrypto | ecrecover | 38.160 | 38.361 | 38.636 |
| SSE2, RustCrypto | verify | 100.018 | 100.695 | 101.270 |
| SSE2, RustCrypto | ecrecover | 38.422 | 38.539 | 38.740 |

| Build | Pass | Verify median (µs) | Ecrecover median (µs) | Ratio |
| --- | ---: | ---: | ---: | ---: |
| native, asm-keccak | 1 | 36.569 | 38.280 | 0.955x |
| native, asm-keccak | 2 | 36.748 | 38.348 | 0.958x |
| native, asm-keccak | 3 | 36.945 | 38.789 | 0.952x |
| native, RustCrypto | 1 | 40.828 | 38.291 | 1.066x |
| native, RustCrypto | 2 | 40.846 | 38.477 | 1.062x |
| native, RustCrypto | 3 | 40.766 | 38.333 | 1.063x |
| SSE2, RustCrypto | 1 | 100.740 | 38.518 | 2.615x |
| SSE2, RustCrypto | 2 | 100.739 | 38.550 | 2.613x |
| SSE2, RustCrypto | 3 | 100.545 | 38.516 | 2.610x |

## Revisions and reproduction

The implementation/harness sources match `9d48d7004cef195fc0558b4c41bd72599db5eb8b`.
The checkout HEAD is `3dcacee12b0926e1beb57518b106a34024406f86`, with existing
documentation and benchmark-runner edits. The implementation was unchanged.
The exact source and binary hashes are retained in the raw data.

The benchmark manifest and lockfile pin leanVM to the revision in the table
below. The historical dataset retains the measured manifest and lockfile hashes.
The shell runner records its own source and platform snapshots for new campaigns.

| Dependency | Pinned revision |
| --- | --- |
| evm2 | `e681662b6d9ec59edafd112f7c8d64f49f1e6dd1` |
| Alloy core | `70a63bd609da78dcf03e593ae772fec883ce7768` |
| leanVM | `6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b` |
| EthLib | `03547dd83f298a63e6dcceff0a0b75f6142490aa` |

Build each configuration separately and preserve its executable before building
the next. Use the default benchmark features for libsecp256k1. Add
`--features asm-keccak` only for the assembly configuration. Native builds use
`RUSTFLAGS='-C target-cpu=native'`; SSE2 uses
`RUSTFLAGS='-C target-cpu=x86-64'`.

```sh
cargo +1.97.1 bench --locked --offline --manifest-path benchmarks/evm2/Cargo.toml --bench matrix --no-run
```

After compilation, pin the executable to the intended logical CPU and run:

```sh
matrix --run --samples 44 --sample-ms 10 --warmup-ms 300 --extra-cases 8 \
  --seed 2026111811 --groups direct,ecrecover --json pass.json --corpus-json corpus.json
```

Repeat in three processes, rotating configuration order and changing the
sampling seed. The raw reports retain the exact seeds, complete corpus,
iteration counts, sample times, resolved build features and compiler metadata.
The [benchmark suite](SUITE.md) also automates build/run separation and
process affinity. Reproducing on Linux changes the toolchain/platform control;
it need not reproduce the Windows numbers.

## Interpreting the gas comparison

| Gas reference | Charge | Status and source |
| --- | ---: | --- |
| Ecrecover precompile | 3,000 | Existing precompile; [EIP-1108 calibration](https://eips.ethereum.org/EIPS/eip-1108#specification) |
| P256VERIFY precompile | 6,900 | [EIP-7951 gas schedule](https://eips.ethereum.org/EIPS/eip-7951#gas-schedule) |
| Native SECP256K1 signature | 2,800 | [Draft EIP-8141](https://eips.ethereum.org/EIPS/eip-8141) |
| Native P256 signature | 6,700 | [Draft EIP-8141](https://eips.ethereum.org/EIPS/eip-8141) |
| Native leanSPHINCS signature | 12,600 | [Draft PR #12616](https://github.com/ethereum/EIPs/pull/12616), older 492-permutation pin |
| Updated leanSPHINCS price | 13,200 | [Review suggestion](https://github.com/ethereum/EIPs/pull/12616#pullrequestreview-5920543343) for 515 permutations |

These are verification charges, excluding signature-data costs and other
transaction work. Draft and review prices are not finalized protocol rules.

CPU time is the local proxy for computational work. Convert it relative to a
measured reference, not through a universal gas-per-second constant:

```text
cpu_work_ratio = verification_time / ecrecover_time
time_equivalent_gas = reference_gas * cpu_work_ratio
checks_per_second = 1,000,000 / median_microseconds_per_check
relative_cpu_time_per_gas = cpu_work_ratio / (scheme_gas / reference_gas)
```

| Rust audit build | CPU-work ratio | Verify checks/s/core | Ecrecover checks/s/core | Gas equivalent at 3,000 | Gas equivalent at 2,800 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Assembly Keccak + MSVC C recovery | 0.957x | 27,222 | 26,050 | 2871 | 2679 |
| Assembly Keccak + Clang C recovery | 1.437x | 27,142 | 39,010 | 4312 | 4024 |
| RustCrypto Keccak + k256 | 0.803x | 24,592 | 19,745 | 2409 | 2248 |

Rates are reciprocals of median batch times. They are not full-node TPS or
measured multicore scaling. These are the 32-ECDSA-input audit rows; the
original campaign's single-fixture rows are retained separately above.

For the faster Clang C reference, 3,000 / 25.634 gives
117.031 gas/µs on this machine. Multiplying by
36.843 µs gives 4312 equivalent gas.
The pure-Rust recovery backend is slower, so its calibration yields a smaller
estimate even though leanSPHINCS verification takes more time in that build.
Backend choice must be recorded alongside the estimate.

[EIP-1108](https://eips.ethereum.org/EIPS/eip-1108#specification) used Ecrecover
runtime as a pricing anchor. Its historical gas/µs value belongs to that
hardware; this table uses the measured reference times on the present CPU.
The native 2,800 reference comes from draft EIP-8141. All figures exclude
signature-data costs, EVM dispatch and transaction handling.

The current [leanSPHINCS proposal](https://github.com/ethereum/EIPs/pull/12616)
arrives at 12,600 gas by pricing the older format's 492 Keccak permutations at
25.5 gas each: 12,546 rounded up. The newer layout implemented here and in
geth's PoC uses 515 permutations. Applying the same rule gives 13,132.5 gas;
an [existing review](https://github.com/ethereum/EIPs/pull/12616#pullrequestreview-5920543343)
suggests 13,200. This also requires updating the proposal's pinned encoding.

These local Rust timings do not support an assertion that 12,600 gas is too
low for this implementation on this CPU. They also do not establish that
12,600 is a safe network-wide price. CPU architecture, compiler, cryptographic
backend and client implementation change the ratio. Native SIMD can process
several independent hashes together, so permutation counts and wall-clock
ratios measure different aspects of cost.

Signature-data costs, bandwidth, transaction handling and adversarial workload
limits require separate measurements. Wallet signing and key-generation time
are not work charged to the network for checking an ordinary signature.

## Auxiliary geth PoC control

A [fresh PR-pinned Go confirmation](go-bench-res.md) records longer samples, both cgo
configurations, all five benchmark operations and complete setup details.

The [Go PoC](https://github.com/ethereum/go-ethereum/pull/36137), pinned at
`3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1`, was also benchmarked on this CPU.
Its package sources were compiled against the existing geth checkout
`14f4be01e9d24659bc241922b2e43beba685554f`. The Keccak, secp256k1 and secp256r1
source-tree hashes match its PR base. Its known-answer signature, malformed
inputs and 515-permutation check passed before timing.

Both configurations use Go 1.27.3 and `GOAMD64=v1`. The first enables cgo
with MinGW GCC 13.2.0; the second disables cgo. Each configuration has three
processes with three one-second repetitions per operation, pinned to CPU 8.
The medians of all nine retained repetitions per configuration are:

| geth configuration | leanSPHINCS verify (µs) | Ecrecover control (µs) | Ratio |
| --- | ---: | ---: | ---: |
| `CGO_ENABLED=1`, GCC C/libsecp256k1 | 130.689 | 28.664 | 4.559x |
| `CGO_ENABLED=0`, Go Decred recovery | 132.766 | 108.800 | 1.220x |

The second row explicitly sets `CGO_ENABLED=0`, selecting geth's Go Decred
recovery implementation. Its known-answer, malformed-input and permutation
checks also pass. Disabling cgo leaves leanSPHINCS verification close to the
first row but makes recovery substantially slower. The posted ARM benchmark
does not record `CGO_ENABLED`; its description of leanSPHINCS as pure Go does
not establish which recovery implementation was used. On amd64, Keccak can
still use Go assembly when cgo is disabled.

The pure-Go samples are included in the [backend audit data](ecrecover-backend-audit-2026-11-18.json).

Go's `crypto.Ecrecover` returns the uncompressed public key without Ethereum
address hashing. evm2's measured provider includes that hash. The two runs also
use different C compilers/backends and CPU-target settings. Keep each timing
ratio paired with its own control; comparing raw times is not an isolated
comparison of programming languages.

## Raw data and earlier results

- [All nine Rust process reports, source/build hashes and auxiliary Go samples](ecrecover-2026-11-18.json).
- [Earlier native signature and recovery matrices](RAW_RESULTS.md).
- [Earlier upstream proving comparison](PROVING_RESULTS.md).
- [Historical 15 November measurements](../BENCHMARKS.md).
- [Harness API boundaries and options](evm2/README.md).
