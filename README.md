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

## Benchmarks

AMD Ryzen 9 8940HX, Windows x86-64 MSVC, Rust 1.97.1. Both libraries use
`target-cpu=native`; lean-sphincs enables `asm-keccak`. Medians include all
132 samples from three processes over eleven shared seed/message pairs.

| Operation | lean-sphincs | leanVM | Speedup |
| --- | ---: | ---: | ---: |
| Verification (µs) | 36.71 | 120.64 | 3.29x |
| Signing (ms) | 88.25 | 118.68 | 1.34x |
| Key generation (ms) | 46.34 | 61.49 | 1.33x |

A [parameter and optimization audit](benchmarks/OPTIMIZATION_AUDIT.md) confirms
identical hash inputs and isolates the verification speedup with batching and
hash-backend controls.

A separate recovery-backend audit uses 32 ECDSA inputs, three processes and
132 samples per configuration on the same CPU:

| Timed Rust configuration | Our verify (µs) | evm2 ecrecover (µs) | Verify / ecrecover |
| --- | ---: | ---: | ---: |
| Assembly Keccak + Clang C/libsecp256k1 | 36.84 | 25.63 | 1.44x |
| RustCrypto Keccak + Rust k256 | 40.66 | 50.65 | 0.80x |

The C recovery compiler materially changes the comparison; the earlier MSVC-C
control took 38.35 µs. These are native CPU timings, excluding transaction-data
costs, and do not determine consensus gas prices.

[Ecrecover comparison, gas references and raw samples](benchmarks/ECRECOVER_RESULTS.md) ·
[Full native matrix](benchmarks/RAW_RESULTS.md) ·
[Upstream proving comparison](benchmarks/PROVING_RESULTS.md) ·
[Reproduction commands](benchmarks/SUITE.md).

CodSpeed tracks regressions in key generation, signing, verification, rejection,
hashing and evm2 ecrecover with SSE2 and AVX2 builds. Its CPU simulation results
are separate from the native wall-clock measurements above.

## License

MIT OR Apache-2.0 for this implementation. EthLib-derived test data is CC0-1.0.
