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
and evm2 ecrecover with RustCrypto and `asm-keccak`. It runs on pushes to `main`,
pull requests and manual dispatch. Its CPU simulation results track regressions;
the tables below report native wall-clock measurements.

```sh
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench codspeed
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench codspeed --features asm-keccak
```

## Native benchmark results

CPU: AMD Ryzen 9 8940HX (16 cores, 32 threads).

Compiler: Rust 1.97.1; LLVM 22.1.6; MSVC target. Optimization level 3,
Thin LTO, one codegen unit. Native CPU and AVX-512 builds were measured;
the full tables record their exact compiler settings.

These are direct calls to each library's unmodified public APIs. **leanVM** means
the native Rust [`lean_sphincs` crate at `4937c851`](https://github.com/leanEthereum/leanVM/tree/4937c851eafb9e93bc7436eebe9e6dc8ae4c227a/crates/lean_sphincs).
It uses its own Keccak implementation, including its AVX-512 single-state path
in these builds. lean-sphincs uses `asm-keccak` for its best results below.

Verification uses each library's native input: encoded signature bytes for
lean-sphincs, and public-key/signature objects prepared before timing for leanVM.
Signing and key generation return each library's native result, with no added
serialization. Both recompute from the seed on every call. The experimental
local SIMD prototype is excluded from these binaries and results.

Best complete medians across three candidate builds, with 44 samples per pass,
three passes and 11 shared key/message pairs. Every timed sample is retained.
Speedup is `(leanVM time / lean-sphincs time - 1) × 100%`, before rounding.

| Operation | lean-sphincs | leanVM (unmodified) | lean-sphincs speedup |
| --- | ---: | ---: | ---: |
| Verification (µs) | 89.09 | 119.29 | +33.9% |
| Signing (ms) | 90.52 | 121.02 | +33.7% |
| Key generation (ms) | 47.01 | 62.42 | +32.8% |

[Full matched-build results](benchmarks/RAW_RESULTS.md),
[raw measurements](benchmarks/raw-api-measurements.json), and
[exact API calls and methodology](benchmarks/SUITE.md#direct-public-api-comparison).

### Ecrecover

Medians from 40 samples per configuration. [Recorded measurements](benchmarks/measurements.json).

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
