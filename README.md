# lean-sphincs

A native Rust implementation of the experimental
leanSPHINCS configuration specified by
[EthLib at `03547dd83f298a63e6dcceff0a0b75f6142490aa`](https://github.com/ethereum/EthLib/tree/03547dd83f298a63e6dcceff0a0b75f6142490aa/EthLib/Cryptography/Sphincs).

The library supports key generation, deterministic signing and verification in
`no_std` environments. Its API uses Alloy types and performs no heap allocation.
The optional `asm-keccak` feature enables assembly-accelerated Keccak hashing.

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
all three operations.

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

Hardware: AMD Ryzen 9 8940HX (16 cores, 32 threads), 32 GB RAM, Windows 11
build 26200. Reported nominal CPU frequency: 2.401 GHz; effective clock speed
was not measured.

Compiler: Rust 1.97.1, LLVM 22.1.6, Windows MSVC, optimization level 3,
Thin LTO and one codegen unit. Library revision: `e0b6b23`.

Signature timings are medians from 30 samples per configuration using three
rotating specification fixtures. The target batch duration was 10 ms; longer
operations ran to completion. Setup, validation and warmup were excluded.

The comparison uses [leanVM's Rust leanSPHINCS implementation](https://github.com/leanEthereum/leanVM/tree/f7ba4999ae523b94c8d0969b32762c3effea4cbd/crates/lean_sphincs)
at `f7ba4999`, compiled with the same CPU target and its own hashing backend.
The full dependency pin is in the [benchmark manifest](benchmarks/evm2/Cargo.toml).

### Verification

| Compiler target | Hash backend | lean-sphincs (µs) | leanVM (µs) |
| --- | --- | ---: | ---: |
| SSE2 | RustCrypto | 100.3 | 141.4 |
| SSE2 | tiny-keccak | 102.8 | 141.3 |
| SSE2 | asm-keccak | 89.1 | 141.5 |
| SSE4.2 | RustCrypto | 147.3 | 236.0 |
| SSE4.2 | tiny-keccak | 150.2 | 236.1 |
| SSE4.2 | asm-keccak | 89.0 | 236.3 |
| AVX2 | RustCrypto | 118.7 | 122.2 |
| AVX2 | tiny-keccak | 117.7 | 121.1 |
| AVX2 | asm-keccak | 99.8 | 119.6 |
| AVX-512 | RustCrypto | 116.0 | 118.5 |
| AVX-512 | tiny-keccak | 245.0 | 121.8 |
| AVX-512 | asm-keccak | 88.9 | 123.3 |
| Ryzen 9 8940HX (native) | RustCrypto | 113.9 | 119.4 |
| Ryzen 9 8940HX (native) | tiny-keccak | 244.5 | 118.8 |
| Ryzen 9 8940HX (native) | asm-keccak | 86.8 | 120.1 |

### Signing

| Compiler target | Hash backend | lean-sphincs (ms) | leanVM (ms) |
| --- | --- | ---: | ---: |
| SSE2 | RustCrypto | 130.2 | 138.9 |
| SSE2 | tiny-keccak | 132.8 | 138.1 |
| SSE2 | asm-keccak | 104.2 | 138.4 |
| SSE4.2 | RustCrypto | 223.8 | 230.9 |
| SSE4.2 | tiny-keccak | 224.7 | 231.5 |
| SSE4.2 | asm-keccak | 103.3 | 231.1 |
| AVX2 | RustCrypto | 113.6 | 116.7 |
| AVX2 | tiny-keccak | 117.6 | 116.5 |
| AVX2 | asm-keccak | 97.0 | 116.8 |
| AVX-512 | RustCrypto | 115.5 | 116.9 |
| AVX-512 | tiny-keccak | 240.7 | 117.5 |
| AVX-512 | asm-keccak | 87.9 | 119.2 |
| Ryzen 9 8940HX (native) | RustCrypto | 111.1 | 115.8 |
| Ryzen 9 8940HX (native) | tiny-keccak | 245.4 | 115.0 |
| Ryzen 9 8940HX (native) | asm-keccak | 86.0 | 117.6 |

### Key generation

| Compiler target | Hash backend | lean-sphincs (ms) | leanVM (ms) |
| --- | --- | ---: | ---: |
| SSE2 | RustCrypto | 69.3 | 74.2 |
| SSE2 | tiny-keccak | 73.3 | 73.8 |
| SSE2 | asm-keccak | 57.7 | 73.6 |
| SSE4.2 | RustCrypto | 119.5 | 123.6 |
| SSE4.2 | tiny-keccak | 119.7 | 124.3 |
| SSE4.2 | asm-keccak | 54.5 | 124.2 |
| AVX2 | RustCrypto | 60.8 | 62.4 |
| AVX2 | tiny-keccak | 63.7 | 62.3 |
| AVX2 | asm-keccak | 51.8 | 62.0 |
| AVX-512 | RustCrypto | 60.4 | 62.2 |
| AVX-512 | tiny-keccak | 129.1 | 63.1 |
| AVX-512 | asm-keccak | 47.0 | 65.0 |
| Ryzen 9 8940HX (native) | RustCrypto | 62.4 | 61.3 |
| Ryzen 9 8940HX (native) | tiny-keccak | 129.2 | 61.4 |
| Ryzen 9 8940HX (native) | asm-keccak | 46.1 | 61.0 |

### Ecrecover

These measurements call evm2's ECDSA recovery provider, including signature
parsing, public-key recovery, serialization and address hashing. Transaction
dispatch and calldata costs are excluded.

Median of 200 samples per configuration, with a 20 ms target batch duration.

#### libsecp256k1 (C)

| Compiler target | RustCrypto (µs) | tiny-keccak (µs) | asm-keccak (µs) |
| --- | ---: | ---: | ---: |
| SSE2 | 90.68 | 83.72 | 84.59 |
| SSE4.2 | 84.11 | 84.08 | 84.31 |
| AVX2 | 94.69 | 83.75 | 83.68 |
| AVX-512 | 90.71 | 84.21 | 90.38 |
| Ryzen 9 8940HX (native) | 91.51 | 93.05 | 89.57 |

#### k256 (Rust)

| Compiler target | RustCrypto (µs) | tiny-keccak (µs) | asm-keccak (µs) |
| --- | ---: | ---: | ---: |
| SSE2 | 110.54 | 110.12 | 133.52 |
| SSE4.2 | 109.10 | 119.30 | 126.95 |
| AVX2 | 108.92 | 119.89 | 124.19 |
| AVX-512 | 124.51 | 122.73 | 118.44 |
| Ryzen 9 8940HX (native) | 110.73 | 111.47 | 121.23 |

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
