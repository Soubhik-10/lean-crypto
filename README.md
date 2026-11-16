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
| Public key | 32 bytes: `PK.seed || PK.root` |
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
arrays. Small addressed hashes reuse a contiguous stack buffer. On baseline
x86-64, independent FORS openings use paired SSE2 Keccak hashing through safe
SIMD types. AVX2 builds and other targets use the selected Alloy backend.

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
and evm2 ecrecover with RustCrypto and `asm-keccak`. It runs on pushes to `main`,
pull requests and manual dispatch. Its CPU simulation results track regressions;
the tables below report native wall-clock measurements.

```sh
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench codspeed
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench codspeed --features asm-keccak
```

## Native benchmark results

CPU: AMD Ryzen 9 8940HX with Radeon Graphics (16 cores, 32 threads).

Compiler: Rust 1.97.1; LLVM 22.1.6. Optimization level 3, Thin LTO, one codegen unit.

Median time per operation from 40 samples per configuration (1 pass). Measured speedup = `(leanVM / lean-sphincs - 1) × 100%`; negative values mean slower.

Verification starts from encoded signatures; signing and key generation include serialization. Small differences need confirmation across repeat runs.

The Keccak column selects lean-sphincs' Alloy backend. Verification also uses paired SSE2 FORS hashing in SSE2 and SSE4.2 builds. leanVM uses its own CPU-selected scalar and SIMD paths. Compiler flags apply to both implementations within each row. See the [measurement method and raw data](benchmarks/SUITE.md#published-measurements).

leanVM: [native Rust leanSPHINCS implementation](https://github.com/leanEthereum/leanVM/tree/f7ba4999ae523b94c8d0969b32762c3effea4cbd/crates/lean_sphincs).

### Verification

| Compiler target | lean-sphincs Keccak | lean-sphincs (µs) | leanVM (µs) | Measured speedup |
| --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | 103.07 | 145.11 | +40.8% |
| SSE2 | tiny-keccak | 102.76 | 146.88 | +42.9% |
| SSE2 | asm-keccak | 94.58 | 145.47 | +53.8% |
| SSE4.2 | RustCrypto | 148.45 | 238.13 | +60.4% |
| SSE4.2 | tiny-keccak | 152.14 | 239.23 | +57.2% |
| SSE4.2 | asm-keccak | 89.95 | 239.33 | +166.1% |
| AVX2 | RustCrypto | 116.17 | 121.27 | +4.4% |
| AVX2 | tiny-keccak | 118.30 | 120.66 | +2.0% |
| AVX2 | asm-keccak | 99.55 | 120.19 | +20.7% |
| AVX-512 | RustCrypto | 122.85 | 120.69 | -1.8% |
| AVX-512 | tiny-keccak | 123.75 | 122.40 | -1.1% |
| AVX-512 | asm-keccak | 89.63 | 121.66 | +35.7% |
| native | RustCrypto | 113.21 | 118.94 | +5.1% |
| native | tiny-keccak | 109.21 | 119.20 | +9.1% |
| native | asm-keccak | 87.06 | 118.37 | +36.0% |

### Signing

| Compiler target | lean-sphincs Keccak | lean-sphincs (ms) | leanVM (ms) | Measured speedup |
| --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | 137.94 | 146.74 | +6.4% |
| SSE2 | tiny-keccak | 132.35 | 140.02 | +5.8% |
| SSE2 | asm-keccak | 117.52 | 151.13 | +28.6% |
| SSE4.2 | RustCrypto | 225.02 | 232.70 | +3.4% |
| SSE4.2 | tiny-keccak | 238.95 | 235.01 | -1.6% |
| SSE4.2 | asm-keccak | 103.67 | 233.59 | +125.3% |
| AVX2 | RustCrypto | 115.62 | 117.41 | +1.5% |
| AVX2 | tiny-keccak | 116.06 | 118.10 | +1.8% |
| AVX2 | asm-keccak | 97.55 | 118.60 | +21.6% |
| AVX-512 | RustCrypto | 122.80 | 120.71 | -1.7% |
| AVX-512 | tiny-keccak | 128.78 | 118.47 | -8.0% |
| AVX-512 | asm-keccak | 88.82 | 117.63 | +32.4% |
| native | RustCrypto | 111.37 | 115.39 | +3.6% |
| native | tiny-keccak | 110.91 | 116.11 | +4.7% |
| native | asm-keccak | 86.34 | 115.88 | +34.2% |

### Key generation

| Compiler target | lean-sphincs Keccak | lean-sphincs (ms) | leanVM (ms) | Measured speedup |
| --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | 71.87 | 76.07 | +5.8% |
| SSE2 | tiny-keccak | 70.30 | 75.03 | +6.7% |
| SSE2 | asm-keccak | 57.70 | 76.96 | +33.4% |
| SSE4.2 | RustCrypto | 120.39 | 124.17 | +3.1% |
| SSE4.2 | tiny-keccak | 122.43 | 126.37 | +3.2% |
| SSE4.2 | asm-keccak | 54.80 | 125.03 | +128.2% |
| AVX2 | RustCrypto | 61.34 | 63.06 | +2.8% |
| AVX2 | tiny-keccak | 61.65 | 63.23 | +2.6% |
| AVX2 | asm-keccak | 51.81 | 63.79 | +23.1% |
| AVX-512 | RustCrypto | 64.55 | 63.36 | -1.9% |
| AVX-512 | tiny-keccak | 63.34 | 63.06 | -0.5% |
| AVX-512 | asm-keccak | 47.15 | 62.35 | +32.2% |
| native | RustCrypto | 59.82 | 61.99 | +3.6% |
| native | tiny-keccak | 58.08 | 61.55 | +6.0% |
| native | asm-keccak | 46.22 | 61.29 | +32.6% |

### Ecrecover

#### evm2 libsecp256k1

| Compiler target | RustCrypto (µs) | tiny-keccak (µs) | asm-keccak (µs) |
| --- | ---: | ---: | ---: |
| SSE2 | 39.17 | 38.52 | 39.50 |
| SSE4.2 | 38.47 | 38.72 | 38.37 |
| AVX2 | 38.45 | 38.72 | 38.27 |
| AVX-512 | 40.40 | 38.94 | 38.62 |
| native | 38.33 | 38.25 | 38.23 |

#### evm2 k256

| Compiler target | RustCrypto (µs) | tiny-keccak (µs) | asm-keccak (µs) |
| --- | ---: | ---: | ---: |
| SSE2 | 50.86 | 50.48 | 50.56 |
| SSE4.2 | 49.89 | 49.92 | 49.92 |
| AVX2 | 49.98 | 51.76 | 49.81 |
| AVX-512 | 50.34 | 51.34 | 50.04 |
| native | 50.46 | 51.00 | 50.44 |

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
