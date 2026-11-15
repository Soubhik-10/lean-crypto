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
The specification rates one key for at most `2^30` signatures; enforcing that
budget belongs to the caller.

## Implementation and provenance

The verifier follows the pinned specification and its documented FIPS 205
deviations.

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

The CodSpeed workflow runs on pushes to `main`, pull requests and manual
dispatch. It tracks key generation, signing, valid verification, late rejection,
Keccak hashing and evm2 ecrecover for both default and assembly Keccak builds.
Backend-specific benchmark names keep the two configurations distinct.

CodSpeed uses CPU simulation for regression tracking. Its results are not native
wall-clock timings or gas prices. The local harness below measures elapsed time.

```sh
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench codspeed
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench codspeed --features asm-keccak
```

## Benchmark against evm2

Measured timings and gas-ratio estimates are in [BENCHMARKS.md](BENCHMARKS.md).

The isolated harness in [benchmarks/evm2](benchmarks/evm2/README.md) calls
`evm2::precompiles::crypto().secp256k1_ecrecover` directly. evm2 is a benchmark
dependency only. It is not a dependency of the core library or its tests.

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
