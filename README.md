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
The scheme and this package remain experimental. The formal CI described below
checks an upstream Lean model and conformance evidence for this implementation;
it does not establish a complete formal proof of the Rust source. No independent
security review or audit is claimed.

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

## Formal verification CI

The [formal workflow](.github/workflows/formal.yml) uses the Lean 4 specification
and security proofs from [leanEthereum/leanVM](https://github.com/leanEthereum/leanVM/tree/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/formal),
pinned to `f95bc21a4875e10a733f4b2e56f1d4adb81536eb` in
[formal/upstream.json](formal/upstream.json). leanVM credits
[Verified-zkEVM/leanerVM](https://github.com/Verified-zkEVM/leanerVM) as the source
of its vendored formalization. The SPHINCS specification is
[`Statement/LeanSphincs.lean`](https://github.com/leanEthereum/leanVM/blob/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/formal/Statement/LeanSphincs.lean);
its security proof is in
[`formal/lean_sphincs`](https://github.com/leanEthereum/leanVM/tree/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/formal/lean_sphincs).

On pull requests and pushes to `main`, CI rebuilds those proofs with the Lean
kernel enabled, rejects proof escapes, and checks that the end theorems use only
`propext`, `Classical.choice` and `Quot.sound`, as upstream CI does. The security
theorem concerns strong unforgeability of the modeled scheme in the
random-permutation model, under its stated assumptions and query bounds.

CI also compares this crate directly with the executable Lean model. It exports
key generation, deterministic signatures and verification results from this
Rust checkout, then requires the model to agree on every case. The corpus
includes all 35 pinned vectors, reproducible generated seeds/messages, signature,
key and message mutations, and malformed lengths. Comparisons run separately
for SSE2/AVX2 and RustCrypto/`asm-keccak`. CI saves the corpus, seed, results,
upstream revision and axiom report for replay. Missing cases fail the job.

The repository also kernel-checks [additional Lean equivalences](formal/Implementation/Algorithms.lean)
for the verifier's index loop, WOTS recovery schedule and bounded least-counter
search, including signing failure at the actual 32-bit counter limit. These are
relationships between Lean algorithm descriptions; they do not prove the compiled
Rust program correct. Component tests compare real production functions with the
same pinned Lean specification and check counter/codeword/tree boundaries and
AVX2 scalar tails. Both real Lean executables must reject deliberately wrong
expected results in every matrix job.

The evidence has three levels: security theorems about the Lean specification,
proved relationships between Lean descriptions, and finite Rust-to-Lean
conformance tests. The new functional equivalences do not transfer oracle-query
security bounds to Rust's different hash-call order. Rust/backend semantics,
compilers and test parsers remain trusted; constant time and side channels are
outside these proofs. [Proof inventory, limits and reproduction](formal/README.md).

The [Rust workflow](.github/workflows/rust.yml) additionally checks formatting,
strict library Clippy, documentation, unused dependencies, the declared Rust 1.90
minimum, `no_std` ARM Cortex-M compilation, SSE2/AVX2/ARM64 tests and macOS/Windows
compilation. Existing CodSpeed benchmarks, differential tests and fuzzing remain
separate checks.

## Benchmarks

AMD Ryzen 9 8940HX, Windows x86-64 MSVC, Rust 1.97.1. Both libraries use
release optimization and native CPU features; our build enables `asm-keccak`.
Each row uses three processes and 132 samples over eleven shared fixtures.

| Operation | lean-sphincs | leanVM | Speedup |
| --- | ---: | ---: | ---: |
| Verification (µs) | 36.91 | 119.28 | 3.23x |
| Signing (ms) | 88.25 | 118.68 | 1.34x |
| Key generation (ms) | 46.34 | 61.49 | 1.33x |

Verification comes from the batching audit; signing/key generation from the
native API confirmation. Each row compares matched builds. The audit confirms
identical hash inputs and isolates a 2.37x gain from batching within one signature.

| Recovery audit configuration | Our verify (µs) | evm2 ecrecover (µs) | Ratio |
| --- | ---: | ---: | ---: |
| Assembly Keccak + Clang C/libsecp256k1 | 36.84 | 25.63 | 1.44x |
| RustCrypto Keccak + Rust k256 | 40.66 | 50.65 | 0.80x |

These native CPU timings exclude transaction work and do not determine gas prices.
[Results and setup](benchmarks/README.md) · [Batching, gains and tradeoffs](benchmarks/BATCHING.md) ·
[Shell benchmark commands](benchmarks/SUITE.md#compare-ours-leanvm-and-ecrecover).

```sh
bash benchmarks/compare.sh native
bash benchmarks/compare.sh backends
```

CodSpeed separately tracks regressions with SSE2 and AVX2 builds.

## License

MIT OR Apache-2.0 for this implementation. EthLib-derived test data is CC0-1.0.
