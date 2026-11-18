# lean-sphincs

A native Rust implementation of the experimental
leanSPHINCS configuration specified by
[EthLib at `03547dd83f298a63e6dcceff0a0b75f6142490aa`](https://github.com/ethereum/EthLib/tree/03547dd83f298a63e6dcceff0a0b75f6142490aa/EthLib/Cryptography/Sphincs).

The library supports key generation, deterministic signing and verification in
`no_std` environments. Its API uses Alloy types and performs no heap allocation.
The optional `asm-keccak` feature enables assembly-accelerated Keccak hashing.

The [beginner guide](docs/guide.md) explains the scheme, implementation and benchmarks.

```rust
use lean_sphincs::{B256, SignError, key_gen, sign, verify};

fn round_trip(secret_seed: &B256, message: &B256) -> Result<(), SignError> {
    let public_key = key_gen(secret_seed);
    let signature = sign(secret_seed, message)?;
    assert!(verify(&public_key, message, signature.as_slice()));
    Ok(())
}
```

The caller supplies a secret seed containing 32 uniformly random bytes and keeps
it secret. Messages are exact 32-byte digests; the caller computes the transaction
hash and signing domain. A seed must sign at most `2^30` messages, including
attestations. The library does not generate randomness or track that budget.

## Configuration

| Item | Value |
| --- | --- |
| Public key | 32 bytes: `PK.seed` followed by `PK.root` |
| Message | 32-byte digest |
| Signature | 7,740 bytes |
| Hash | Ethereum Keccak-256, truncated to 16 bytes for tree values |
| FORS | 24 trees, each height 10 |
| WOTS+C | 64 base-4 digits, target sum 128 |
| Hypertree heights | 8, 8, 10, bottom first |
| Valid verification | 515 Keccak-f[1600] permutations |

This is not a verifier for the standard FIPS 205 SHA2/SHAKE parameter sets.
Older leanSPHINCS layouts using `root || public parameter` are incompatible.

## Implementation and provenance

The implementation reads fixed-size signature fields in place. FORS roots and
WOTS chain ends are streamed into Alloy hashers instead of collecting temporary
arrays. Small addressed hashes reuse a contiguous stack buffer. On
x86-64, verification batches independent FORS openings using two SSE2 lanes.
AVX2 builds use four lanes for FORS and batch active WOTS+C chains within a
small window. Both paths use safe SIMD types and stream results in signature
order. Other targets use the selected Alloy backend.

Signing builds each tree once. A roughly 32 KiB stack cache retains the public
nodes of the top tree so its root and selected authentication path share the
same computation. Key generation uses a streaming tree builder with a small
stack instead of retaining the full tree.

Conformance fixtures are derived from EthLib's CC0-1.0 test data, with source
revision and raw-file hashes retained in [tests/vectors](tests/vectors/README.md).
No claim of independent security review, audit, or formal verification is made.
The scheme and this package remain experimental.

## Validation

```sh
cargo test --release
cargo test --release --features asm-keccak
cargo check --lib --no-default-features
cargo clippy --all-targets --all-features -- -D warnings
cargo doc --no-deps --all-features
```

Tests cover all 35 pinned key-generation, signing and verification vectors,
byte-for-byte deterministic signatures, round trips, counter-exhaustion errors,
every-byte mutation checks, malformed encodings, and zero allocations across
all three operations. The [differential test runner](testing/README.md) and
[coverage-guided fuzzers](fuzz/README.md) compare this crate with leanVM.

## Continuous benchmarks

CodSpeed tracks key generation, signing, verification, rejection, Keccak hashing
and evm2 ecrecover with RustCrypto and `asm-keccak`, with separate SSE2 and AVX2
builds. It runs on pushes to `main`,
pull requests and manual dispatch. Its CPU simulation results track regressions;
the tables below report native wall-clock measurements.

```sh
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench codspeed
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench codspeed --features asm-keccak
```

## Native benchmark results

CPU: AMD Ryzen 9 8940HX (16 cores, 32 threads).

Compiler: Rust 1.97.1; LLVM 22.1.6; x86-64 MSVC target. Optimization level 3,
Thin LTO, one codegen unit.

Direct public APIs of this crate and the unmodified native Rust
[`lean_sphincs` package from leanVM at `6a828ecf`](https://github.com/leanEthereum/leanVM/tree/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b/crates/lean_sphincs).
leanVM has no optional signature/hash Cargo features; compiler target flags
select its own Keccak implementation. The Keccak labels below select our
Alloy backend and do not change leanVM's backend. `experimental-simd` is excluded.

Verification receives encoded bytes in lean-sphincs and native public-key/signature
objects prepared before timing in leanVM. Signing and key generation return
native results and recompute from the seed on every call. No local adapter,
added serialization, or proof-generation work is timed in these tables.

Headline values are each implementation's fastest confirmed complete median:
44 samples per pass, three passes and 11 shared key/message pairs. All samples
are retained. Faster = `(leanVM time / lean-sphincs time − 1) × 100%`, calculated
before rounding. Negative values mean slower.

| Operation | lean-sphincs | leanVM (unmodified) | Faster than leanVM |
| --- | ---: | ---: | ---: |
| Verification (µs) | 35.88 | 119.91 | +234.2% |
| Signing (ms) | 87.93 | 119.64 | +36.1% |
| Key generation (ms) | 46.36 | 61.87 | +33.5% |

[Exact revisions, features, APIs and reproduction](benchmarks/BENCHMARK_SETUP.md) ·
[Winning builds and matched results](benchmarks/RAW_RESULTS.md) ·
[Every confirmation sample](benchmarks/raw-api-measurements.json).

### Three-pass confirmation details

132 samples per operation and build. Compiler flags apply to both libraries in each row.

#### Verification

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (µs) | leanVM (µs) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| AVX-512 | asm-keccak | enabled | 35.88 | 121.62 | +239.0% |
| native | RustCrypto | disabled | 41.28 | 120.91 | +192.9% |
| native | tiny-keccak | disabled | 40.74 | 121.09 | +197.2% |
| native | asm-keccak | enabled | 36.70 | 121.89 | +232.1% |
| native | asm-keccak | disabled | 36.55 | 119.91 | +228.1% |

#### Signing

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| AVX-512 | asm-keccak | enabled | 89.91 | 119.64 | +33.1% |
| native | RustCrypto | disabled | 112.27 | 120.59 | +7.4% |
| native | tiny-keccak | disabled | 113.51 | 122.02 | +7.5% |
| native | asm-keccak | enabled | 87.93 | 121.52 | +38.2% |
| native | asm-keccak | disabled | 89.07 | 120.54 | +35.3% |

#### Key generation

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| AVX-512 | asm-keccak | enabled | 47.15 | 63.15 | +33.9% |
| native | RustCrypto | disabled | 58.88 | 62.14 | +5.5% |
| native | tiny-keccak | disabled | 58.74 | 62.17 | +5.8% |
| native | asm-keccak | enabled | 46.36 | 61.87 | +33.5% |
| native | asm-keccak | disabled | 46.79 | 62.27 | +33.1% |

### Full build matrix

44 samples per case and configuration, over the same 11 signature inputs.
The Keccak column selects lean-sphincs' Alloy backend; leanVM uses its own
CPU-selected hashing implementation. LLVM SLP is automatic compiler vectorization;
disabling it leaves explicit SIMD enabled.

#### Verification

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (µs) | leanVM (µs) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 100.49 | 141.74 | +41.0% |
| SSE2 | tiny-keccak | enabled | 104.03 | 142.30 | +36.8% |
| SSE2 | asm-keccak | enabled | 89.52 | 141.93 | +58.5% |
| SSE4.2 | RustCrypto | enabled | 148.74 | 236.86 | +59.2% |
| SSE4.2 | tiny-keccak | enabled | 151.13 | 237.34 | +57.0% |
| SSE4.2 | asm-keccak | enabled | 89.49 | 239.14 | +167.2% |
| AVX2 | RustCrypto | enabled | 52.81 | 120.49 | +128.2% |
| AVX2 | tiny-keccak | disabled | 72.74 | 119.17 | +63.8% |
| AVX2 | asm-keccak | enabled | 49.85 | 120.25 | +141.2% |
| AVX-512 | RustCrypto | enabled | 40.61 | 119.30 | +193.8% |
| AVX-512 | tiny-keccak | disabled | 40.84 | 120.80 | +195.8% |
| AVX-512 | asm-keccak | enabled | 35.75 | 122.89 | +243.8% |
| native | RustCrypto | enabled | 41.05 | 119.72 | +191.6% |
| native | tiny-keccak | disabled | 41.17 | 123.58 | +200.2% |
| native | asm-keccak | enabled | 36.59 | 118.09 | +222.7% |

#### Signing

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 132.47 | 141.30 | +6.7% |
| SSE2 | tiny-keccak | enabled | 134.31 | 141.63 | +5.5% |
| SSE2 | asm-keccak | enabled | 104.99 | 141.27 | +34.6% |
| SSE4.2 | RustCrypto | enabled | 228.62 | 235.02 | +2.8% |
| SSE4.2 | tiny-keccak | enabled | 229.69 | 235.88 | +2.7% |
| SSE4.2 | asm-keccak | enabled | 105.20 | 236.18 | +124.5% |
| AVX2 | RustCrypto | enabled | 118.73 | 118.40 | -0.3% |
| AVX2 | tiny-keccak | disabled | 117.30 | 119.84 | +2.2% |
| AVX2 | asm-keccak | enabled | 99.49 | 119.48 | +20.1% |
| AVX-512 | RustCrypto | enabled | 114.72 | 119.56 | +4.2% |
| AVX-512 | tiny-keccak | disabled | 120.71 | 119.80 | -0.8% |
| AVX-512 | asm-keccak | enabled | 89.39 | 119.89 | +34.1% |
| native | RustCrypto | enabled | 114.37 | 118.58 | +3.7% |
| native | tiny-keccak | disabled | 112.03 | 118.98 | +6.2% |
| native | asm-keccak | enabled | 87.32 | 117.36 | +34.4% |

#### Key generation

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 69.65 | 74.21 | +6.6% |
| SSE2 | tiny-keccak | enabled | 70.19 | 74.45 | +6.1% |
| SSE2 | asm-keccak | enabled | 54.75 | 74.13 | +35.4% |
| SSE4.2 | RustCrypto | enabled | 120.04 | 124.62 | +3.8% |
| SSE4.2 | tiny-keccak | enabled | 122.01 | 124.61 | +2.1% |
| SSE4.2 | asm-keccak | enabled | 54.98 | 124.63 | +126.7% |
| AVX2 | RustCrypto | enabled | 62.77 | 62.40 | -0.6% |
| AVX2 | tiny-keccak | disabled | 61.20 | 62.31 | +1.8% |
| AVX2 | asm-keccak | enabled | 51.98 | 62.70 | +20.6% |
| AVX-512 | RustCrypto | enabled | 60.43 | 62.35 | +3.2% |
| AVX-512 | tiny-keccak | disabled | 63.85 | 63.21 | -1.0% |
| AVX-512 | asm-keccak | enabled | 47.12 | 62.33 | +32.3% |
| native | RustCrypto | enabled | 59.60 | 62.58 | +5.0% |
| native | tiny-keccak | disabled | 58.33 | 61.94 | +6.2% |
| native | asm-keccak | enabled | 46.15 | 63.19 | +36.9% |

### Ecrecover

Direct calls to evm2's public `Crypto::secp256k1_ecrecover` provider. This includes
ECDSA parsing, public-key recovery, serialization and address hashing, with EVM
dispatch and calldata excluded. Each provider's fastest confirmed median is shown.

| Recovery implementation | Time (µs) | Faster than k256 |
| --- | ---: | ---: |
| libsecp256k1 (C) | 38.35 | +30.3% |
| k256 (Rust) | 49.97 | — |

#### Three-pass recovery confirmation

132 samples per build across three passes.

| Compiler target | Address Keccak | LLVM SLP | Recovery implementation | Time (µs) |
| --- | --- | --- | --- | ---: |
| SSE4.2 | tiny-keccak | enabled | k256 | 50.28 |
| SSE4.2 | asm-keccak | enabled | k256 | 49.97 |
| AVX-512 | asm-keccak | enabled | libsecp256k1 | 38.39 |
| native | RustCrypto | disabled | libsecp256k1 | 38.35 |
| native | tiny-keccak | disabled | libsecp256k1 | 38.36 |
| native | asm-keccak | enabled | libsecp256k1 | 38.35 |
| native | asm-keccak | disabled | libsecp256k1 | 38.39 |

#### All recovery builds

44 samples per configuration. Percentages compare providers with matching
compiler target, address-hashing backend and SLP setting.

| Compiler target | Address Keccak | LLVM SLP | libsecp256k1 (µs) | k256 (µs) | libsecp256k1 faster |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 38.55 | 50.41 | +30.8% |
| SSE2 | tiny-keccak | enabled | 38.50 | 50.84 | +32.1% |
| SSE2 | asm-keccak | enabled | 38.29 | 50.40 | +31.6% |
| SSE4.2 | RustCrypto | enabled | 38.39 | 49.87 | +29.9% |
| SSE4.2 | tiny-keccak | enabled | 38.45 | 50.13 | +30.4% |
| SSE4.2 | asm-keccak | enabled | 38.36 | 49.84 | +29.9% |
| AVX2 | RustCrypto | enabled | 38.41 | 49.88 | +29.9% |
| AVX2 | tiny-keccak | disabled | 38.47 | 51.53 | +33.9% |
| AVX2 | asm-keccak | enabled | 38.54 | 49.87 | +29.4% |
| AVX-512 | RustCrypto | enabled | 38.32 | 50.04 | +30.6% |
| AVX-512 | tiny-keccak | disabled | 38.24 | 51.32 | +34.2% |
| AVX-512 | asm-keccak | enabled | 38.31 | 50.07 | +30.7% |
| native | RustCrypto | enabled | 38.35 | 50.36 | +31.3% |
| native | tiny-keccak | disabled | 38.39 | 50.96 | +32.8% |
| native | asm-keccak | enabled | 38.23 | 50.51 | +32.1% |

[Full matrix measurements](benchmarks/raw-api-matrix.json).

## leanVM proving results

Unmodified upstream `leanvm-cli`, compiled with `target-cpu=native` on the same
AMD Ryzen 9 8940HX. Rust 1.97.1; LLVM 22.1.6; Linux GNU target under WSL2.
Optimization level 3, Thin LTO, one codegen unit. The CLI builds both prover
implementations; `--prover stable` or `--prover experimental` selects one at runtime.
Its upstream `aggregation/signers-cache` feature is enabled.

The current revision is [`6a828ecf`](https://github.com/leanEthereum/leanVM/tree/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b);
the previous pin is [`4937c851`](https://github.com/leanEthereum/leanVM/tree/4937c851eafb9e93bc7436eebe9e6dc8ae4c227a).
Both already include [PR #758](https://github.com/leanEthereum/leanVM/pull/758).
These are upstream implementation names, not production-readiness guarantees.
This crate has no aggregate prover; the following tables compare leanVM variants.
The CLI workloads execute the upstream verification programs.

Proving times are means of all five retained stock CLI passes after one warmup.
Pass times are printed to millisecond precision. Verification uses the CLI's
five-pass mean. WHIR `--log-inv-rate 1` is identical for every run. Recursive
times cover the parent proof over two children; constructing the child proofs
is excluded. Faster = `(baseline time / compared time − 1) × 100%`.
Negative values mean slower.

The experimental prover is faster in all six current workload/worker pairs.
The newer revision does not improve every proving case, and its proof-verification
times are higher in every measured pair below. These are observed timings;
small differences do not establish statistical significance.

### Current stable versus experimental

| Workload | Workers | Stable (s) | Experimental (s) | Experimental faster |
| --- | ---: | ---: | ---: | ---: |
| 16 leanSPHINCS signatures | 1 | 0.4904 | 0.3112 | +57.6% |
| 16 leanSPHINCS signatures | 16 | 0.1532 | 0.1054 | +45.4% |
| 128 leanXMSS signatures | 1 | 0.7440 | 0.4586 | +62.2% |
| 128 leanXMSS signatures | 16 | 0.1952 | 0.1420 | +37.5% |
| Recursive: 2 × 16 leanSPHINCS | 1 | 1.0508 | 0.6798 | +54.6% |
| Recursive: 2 × 16 leanSPHINCS | 16 | 0.3010 | 0.1910 | +57.6% |

### Previous versus current revision

| Workload | Workers | Prover | Previous (s) | Current (s) | Current faster |
| --- | ---: | --- | ---: | ---: | ---: |
| 16 leanSPHINCS signatures | 1 | stable | 0.4702 | 0.4904 | -4.1% |
| 16 leanSPHINCS signatures | 1 | experimental | 0.3018 | 0.3112 | -3.0% |
| 16 leanSPHINCS signatures | 16 | stable | 0.1466 | 0.1532 | -4.3% |
| 16 leanSPHINCS signatures | 16 | experimental | 0.1134 | 0.1054 | +7.6% |
| 128 leanXMSS signatures | 1 | stable | 0.7934 | 0.7440 | +6.6% |
| 128 leanXMSS signatures | 1 | experimental | 0.4804 | 0.4586 | +4.8% |
| 128 leanXMSS signatures | 16 | stable | 0.2028 | 0.1952 | +3.9% |
| 128 leanXMSS signatures | 16 | experimental | 0.1496 | 0.1420 | +5.4% |
| Recursive: 2 × 16 leanSPHINCS | 1 | stable | 1.1324 | 1.0508 | +7.8% |
| Recursive: 2 × 16 leanSPHINCS | 1 | experimental | 0.7656 | 0.6798 | +12.6% |
| Recursive: 2 × 16 leanSPHINCS | 16 | stable | 0.3006 | 0.3010 | -0.1% |
| Recursive: 2 × 16 leanSPHINCS | 16 | experimental | 0.2050 | 0.1910 | +7.3% |

### All proving measurements

| Revision | Workload | Workers | Prover | Proving (s) | Verification (ms) | Proof (KiB) | Peak RSS (GiB) |
| --- | --- | ---: | --- | ---: | ---: | ---: | ---: |
| previous | 16 leanSPHINCS signatures | 1 | stable | 0.4702 | 7.228 | 219.1 | 0.399 |
| previous | 16 leanSPHINCS signatures | 1 | experimental | 0.3018 | 7.299 | 219.1 | 0.413 |
| previous | 16 leanSPHINCS signatures | 16 | stable | 0.1466 | 7.386 | 219.1 | 0.484 |
| previous | 16 leanSPHINCS signatures | 16 | experimental | 0.1134 | 7.257 | 219.1 | 0.504 |
| previous | 128 leanXMSS signatures | 1 | stable | 0.7934 | 7.245 | 242.8 | 0.565 |
| previous | 128 leanXMSS signatures | 1 | experimental | 0.4804 | 6.972 | 242.8 | 0.585 |
| previous | 128 leanXMSS signatures | 16 | stable | 0.2028 | 7.765 | 242.8 | 0.681 |
| previous | 128 leanXMSS signatures | 16 | experimental | 0.1496 | 7.514 | 242.8 | 0.673 |
| previous | Recursive: 2 × 16 leanSPHINCS | 1 | stable | 1.1324 | 8.899 | 272.5 | 0.819 |
| previous | Recursive: 2 × 16 leanSPHINCS | 1 | experimental | 0.7656 | 8.895 | 272.5 | 0.841 |
| previous | Recursive: 2 × 16 leanSPHINCS | 16 | stable | 0.3006 | 9.804 | 272.5 | 0.917 |
| previous | Recursive: 2 × 16 leanSPHINCS | 16 | experimental | 0.2050 | 9.207 | 272.5 | 0.947 |
| current | 16 leanSPHINCS signatures | 1 | stable | 0.4904 | 8.975 | 219.1 | 0.399 |
| current | 16 leanSPHINCS signatures | 1 | experimental | 0.3112 | 9.865 | 219.1 | 0.415 |
| current | 16 leanSPHINCS signatures | 16 | stable | 0.1532 | 9.883 | 219.1 | 0.484 |
| current | 16 leanSPHINCS signatures | 16 | experimental | 0.1054 | 9.580 | 219.1 | 0.516 |
| current | 128 leanXMSS signatures | 1 | stable | 0.7440 | 9.932 | 244.7 | 0.553 |
| current | 128 leanXMSS signatures | 1 | experimental | 0.4586 | 9.576 | 244.7 | 0.577 |
| current | 128 leanXMSS signatures | 16 | stable | 0.1952 | 9.412 | 244.7 | 0.663 |
| current | 128 leanXMSS signatures | 16 | experimental | 0.1420 | 9.547 | 244.7 | 0.777 |
| current | Recursive: 2 × 16 leanSPHINCS | 1 | stable | 1.0508 | 12.382 | 271.0 | 0.803 |
| current | Recursive: 2 × 16 leanSPHINCS | 1 | experimental | 0.6798 | 11.818 | 271.0 | 0.831 |
| current | Recursive: 2 × 16 leanSPHINCS | 16 | stable | 0.3010 | 13.110 | 271.0 | 0.898 |
| current | Recursive: 2 × 16 leanSPHINCS | 16 | experimental | 0.1910 | 12.846 | 271.0 | 0.944 |

Peak RSS is the parent process lifetime peak; it excludes child-process memory.
[Setup and exact API boundaries](benchmarks/BENCHMARK_SETUP.md) ·
[Every proving sample and stock CLI report](benchmarks/proving-measurements.json).

## Benchmark against evm2

Earlier measurements and the gas-ratio methodology are in [BENCHMARKS.md](BENCHMARKS.md).

The [benchmark harness](benchmarks/evm2/README.md) calls
`evm2::precompiles::crypto().secp256k1_ecrecover` directly. evm2 is a benchmark
dependency only.

The harness fetches evm2 from `alloy-rs/evm2` at
`e681662b6d9ec59edafd112f7c8d64f49f1e6dd1`. Alloy types and hashing are pinned
to `alloy-rs/core` at `70a63bd609da78dcf03e593ae772fec883ce7768` in both
packages. No neighboring checkout is required. Both lockfiles are included
with the source; update Git revisions deliberately when changing the comparison.

```sh
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench verify -- \
  --samples 30 --sample-ms 100 --json benchmarks/portable.json
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench verify \
  --features asm-keccak -- \
  --samples 30 --sample-ms 100 --json benchmarks/asm-keccak.json
```

Timings are for verification and ecrecover work, not complete transaction cost.
The wall-clock harness also measures complete signing and key generation.
It reports `3000 * verify_time / ecrecover_time` and, separately,
`2800 * verify_time / ecrecover_time` for the frame-signature baseline. These
are local calibration estimates, not recommended or agreed consensus gas costs.
Signature calldata, bandwidth, aggregation, and cross-client/hardware variation
require separate analysis.

## License

MIT OR Apache-2.0 for this implementation. EthLib-derived test data is CC0-1.0.
