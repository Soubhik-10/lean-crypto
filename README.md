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

Direct public API calls to this crate and the unmodified native Rust
[`lean_sphincs` crate from leanVM at `4937c851`](https://github.com/leanEthereum/leanVM/tree/4937c851eafb9e93bc7436eebe9e6dc8ae4c227a/crates/lean_sphincs).
Verification receives encoded bytes in lean-sphincs and native public-key/signature
objects prepared before timing in leanVM. Signing and key generation return
native results and recompute from the seed on every call. No adapter code or
added serialization is timed.

Each cell reports the median from that implementation's fastest confirmed build
for the operation: 44 samples per pass, three passes and 11 shared key/message pairs.
All samples are retained. Faster = `(leanVM time / lean-sphincs time - 1) × 100%`,
calculated before rounding.

| Operation | lean-sphincs | leanVM (unmodified) | Faster than leanVM |
| --- | ---: | ---: | ---: |
| Verification (µs) | 36.64 | 119.05 | +224.9% |
| Signing (ms) | 89.32 | 119.40 | +33.7% |
| Key generation (ms) | 46.51 | 62.03 | +33.4% |

lean-sphincs uses `asm-keccak` in its fastest builds. leanVM uses its own
Keccak code, including AVX-512 single-state hashing in the fastest confirmed builds. Compiler flags apply to both
libraries within each build.

[Build configurations and matched results](benchmarks/RAW_RESULTS.md),
[raw measurements](benchmarks/raw-api-measurements.json), and
[exact API calls and methodology](benchmarks/SUITE.md#direct-public-api-comparison).

### Three-pass confirmation details

132 samples per operation and build, over three passes. Units are shown in the operation column.

| Operation | Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs | leanVM | Faster than leanVM |
| --- | --- | --- | --- | ---: | ---: | ---: |
| Verification (µs) | native | asm-keccak | enabled | 36.87 | 119.79 | +224.9% |
| Verification (µs) | native | asm-keccak | disabled | 36.68 | 119.05 | +224.5% |
| Verification (µs) | native | RustCrypto | disabled | 41.84 | 121.57 | +190.6% |
| Verification (µs) | AVX-512 | asm-keccak | enabled | 36.64 | 122.25 | +233.6% |
| Signing (ms) | native | asm-keccak | enabled | 89.32 | 119.40 | +33.7% |
| Signing (ms) | native | asm-keccak | disabled | 90.01 | 120.40 | +33.8% |
| Signing (ms) | native | RustCrypto | disabled | 118.13 | 120.22 | +1.8% |
| Signing (ms) | AVX-512 | asm-keccak | enabled | 92.87 | 122.31 | +31.7% |
| Key generation (ms) | native | asm-keccak | enabled | 46.51 | 62.03 | +33.4% |
| Key generation (ms) | native | asm-keccak | disabled | 46.76 | 62.78 | +34.3% |
| Key generation (ms) | native | RustCrypto | disabled | 60.46 | 62.44 | +3.3% |
| Key generation (ms) | AVX-512 | asm-keccak | enabled | 47.58 | 63.44 | +33.3% |

### Full build matrix

44 samples per case and configuration, using the same 11 signature inputs.
Every row calls the unmodified public APIs. The Keccak column selects
lean-sphincs' Alloy backend; leanVM uses its own CPU-selected hashing code.
LLVM SLP is automatic compiler vectorization; disabling it preserves explicit SIMD.

#### Verification

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (µs) | leanVM (µs) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 102.43 | 143.97 | +40.5% |
| SSE2 | tiny-keccak | enabled | 106.97 | 143.23 | +33.9% |
| SSE2 | asm-keccak | enabled | 91.09 | 143.22 | +57.2% |
| SSE4.2 | RustCrypto | enabled | 151.26 | 242.61 | +60.4% |
| SSE4.2 | tiny-keccak | enabled | 154.65 | 242.92 | +57.1% |
| SSE4.2 | asm-keccak | enabled | 91.33 | 242.83 | +165.9% |
| AVX2 | RustCrypto | enabled | 91.42 | 121.46 | +32.9% |
| AVX2 | tiny-keccak | disabled | 71.23 | 122.79 | +72.4% |
| AVX2 | asm-keccak | enabled | 50.49 | 121.65 | +140.9% |
| AVX-512 | RustCrypto | enabled | 41.61 | 121.12 | +191.1% |
| AVX-512 | tiny-keccak | disabled | 41.84 | 123.31 | +194.7% |
| AVX-512 | asm-keccak | enabled | 36.51 | 122.10 | +234.4% |
| native | RustCrypto | enabled | 41.73 | 121.75 | +191.7% |
| native | tiny-keccak | disabled | 41.46 | 122.14 | +194.6% |
| native | asm-keccak | enabled | 36.73 | 118.99 | +224.0% |

#### Signing

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 135.73 | 143.94 | +6.0% |
| SSE2 | tiny-keccak | enabled | 137.84 | 144.09 | +4.5% |
| SSE2 | asm-keccak | enabled | 108.02 | 143.92 | +33.2% |
| SSE4.2 | RustCrypto | enabled | 235.22 | 246.57 | +4.8% |
| SSE4.2 | tiny-keccak | enabled | 236.09 | 244.14 | +3.4% |
| SSE4.2 | asm-keccak | enabled | 106.63 | 242.49 | +127.4% |
| AVX2 | RustCrypto | enabled | 119.95 | 123.58 | +3.0% |
| AVX2 | tiny-keccak | disabled | 121.25 | 121.96 | +0.6% |
| AVX2 | asm-keccak | enabled | 102.17 | 121.22 | +18.7% |
| AVX-512 | RustCrypto | enabled | 117.60 | 121.30 | +3.2% |
| AVX-512 | tiny-keccak | disabled | 121.35 | 122.40 | +0.9% |
| AVX-512 | asm-keccak | enabled | 92.01 | 122.20 | +32.8% |
| native | RustCrypto | enabled | 116.56 | 120.91 | +3.7% |
| native | tiny-keccak | disabled | 112.56 | 123.72 | +9.9% |
| native | asm-keccak | enabled | 88.00 | 117.41 | +33.4% |

#### Key generation

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 70.80 | 75.54 | +6.7% |
| SSE2 | tiny-keccak | enabled | 73.38 | 75.63 | +3.1% |
| SSE2 | asm-keccak | enabled | 55.30 | 75.94 | +37.3% |
| SSE4.2 | RustCrypto | enabled | 122.99 | 127.29 | +3.5% |
| SSE4.2 | tiny-keccak | enabled | 123.98 | 127.38 | +2.7% |
| SSE4.2 | asm-keccak | enabled | 55.58 | 127.02 | +128.5% |
| AVX2 | RustCrypto | enabled | 62.09 | 64.23 | +3.5% |
| AVX2 | tiny-keccak | disabled | 64.52 | 63.37 | -1.8% |
| AVX2 | asm-keccak | enabled | 53.05 | 64.74 | +22.0% |
| AVX-512 | RustCrypto | enabled | 61.21 | 64.03 | +4.6% |
| AVX-512 | tiny-keccak | disabled | 63.36 | 63.95 | +0.9% |
| AVX-512 | asm-keccak | enabled | 48.07 | 64.94 | +35.1% |
| native | RustCrypto | enabled | 60.43 | 63.22 | +4.6% |
| native | tiny-keccak | disabled | 60.72 | 63.51 | +4.6% |
| native | asm-keccak | enabled | 46.48 | 62.47 | +34.4% |

### Ecrecover

Direct calls to `evm2::precompiles::crypto().secp256k1_ecrecover`, using each
provider's fastest confirmed build and the same 132-sample measurement scheme.

| Recovery implementation | Time (µs) | Faster than k256 |
| --- | ---: | ---: |
| libsecp256k1 (C) | 38.67 | +31.5% |
| k256 (Rust) | 50.84 | — |

#### Three-pass recovery confirmation

132 samples per build across three passes.

| Compiler target | Address Keccak | LLVM SLP | Recovery implementation | Time (µs) |
| --- | --- | --- | --- | ---: |
| native | asm-keccak | enabled | libsecp256k1 | 38.86 |
| native | asm-keccak | disabled | libsecp256k1 | 38.67 |
| native | RustCrypto | disabled | libsecp256k1 | 38.90 |
| SSE4.2 | tiny-keccak | enabled | k256 | 50.84 |
| AVX2 | asm-keccak | enabled | k256 | 52.72 |
| AVX-512 | asm-keccak | enabled | libsecp256k1 | 39.16 |

#### All recovery builds

| Compiler target | Address Keccak | LLVM SLP | libsecp256k1 (µs) | k256 (µs) | libsecp256k1 faster |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 39.24 | 51.68 | +31.7% |
| SSE2 | tiny-keccak | enabled | 39.21 | 51.83 | +32.2% |
| SSE2 | asm-keccak | enabled | 39.06 | 51.41 | +31.6% |
| SSE4.2 | RustCrypto | enabled | 39.26 | 50.74 | +29.3% |
| SSE4.2 | tiny-keccak | enabled | 39.25 | 50.61 | +28.9% |
| SSE4.2 | asm-keccak | enabled | 39.02 | 50.85 | +30.3% |
| AVX2 | RustCrypto | enabled | 39.03 | 50.93 | +30.5% |
| AVX2 | tiny-keccak | disabled | 39.15 | 52.34 | +33.7% |
| AVX2 | asm-keccak | enabled | 39.03 | 50.77 | +30.1% |
| AVX-512 | RustCrypto | enabled | 38.66 | 50.95 | +31.8% |
| AVX-512 | tiny-keccak | disabled | 39.01 | 52.04 | +33.4% |
| AVX-512 | asm-keccak | enabled | 38.88 | 51.12 | +31.5% |
| native | RustCrypto | enabled | 39.09 | 50.81 | +30.0% |
| native | tiny-keccak | disabled | 39.07 | 52.07 | +33.3% |
| native | asm-keccak | enabled | 38.51 | 51.49 | +33.7% |

44 samples per configuration. Percentages compare the two providers with matching
compiler and address-hashing settings. [Full matrix measurements](benchmarks/raw-api-matrix.json).

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
