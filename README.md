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

## Native benchmark results

Measured on 16 November 2026 using an AMD Ryzen 9 8940HX (16 cores,
32 threads), 32 GB RAM and Windows 11 build 26200. All configurations ran
on the same machine, pinned to logical CPU 2, on AC power with the Balanced
power plan and Aggressive processor boost enabled. Windows reported a nominal
2.401 GHz; effective boost clocks were not measured.

Compiled with Rust 1.97.1 and LLVM 22.1.6 for Windows MSVC, optimization level 3,
thin LTO and one codegen unit. Library revision: `e0b6b23`.
Each case collected 30 samples in one pass,
with a 10 ms target batch duration and three rotating specification fixtures.
Longer operations ran to completion. Fixture validation, warmup and calibration
were excluded from timing. All samples were retained.

Values are median time per operation. **Lower is faster.** Microseconds are
written as µs; milliseconds as ms. This short run is an initial comparison;
it does not establish stable rankings across CPU settings.

The compilation settings control which instructions the compiler may use:

- **Broad CPU support:** baseline x86-64 instructions, including SSE2.
- **Extra CPU instructions:** adds instructions including SSE4.2 and POPCNT.
- **256-bit vector instructions:** additionally allows AVX2, FMA and related instructions.
- **512-bit vector instructions:** additionally allows AVX-512 instructions.
- **Tuned for this Ryzen:** enables host-specific instructions and compiler tuning.

The hashing choices are **Default Rust** (RustCrypto), **Alternative Rust**
(`tiny-keccak`) and **Assembly** (`asm-keccak`). These choices select this
crate's hashing backend. The reference uses its own hashing implementation
with the same compilation setting; its pinned dependency is recorded in the
[benchmark manifest](benchmarks/evm2/Cargo.toml).

Verification includes reading the encoded signature. Signing and key generation
measure the complete operations from the secret seed.

| Compilation setting | Hashing | Library verify (µs) | Reference verify (µs) | Library sign (ms) | Reference sign (ms) | Library keygen (ms) | Reference keygen (ms) |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Broad CPU support | Default Rust | 100.3 | 141.4 | 130.2 | 138.9 | 69.3 | 74.2 |
| Broad CPU support | Alternative Rust | 102.8 | 141.3 | 132.8 | 138.1 | 73.3 | 73.8 |
| Broad CPU support | Assembly | 89.1 | 141.5 | 104.2 | 138.4 | 57.7 | 73.6 |
| Extra CPU instructions | Default Rust | 147.3 | 236.0 | 223.8 | 230.9 | 119.5 | 123.6 |
| Extra CPU instructions | Alternative Rust | 150.2 | 236.1 | 224.7 | 231.5 | 119.7 | 124.3 |
| Extra CPU instructions | Assembly | 89.0 | 236.3 | 103.3 | 231.1 | 54.5 | 124.2 |
| 256-bit vector instructions | Default Rust | 118.7 | 122.2 | 113.6 | 116.7 | 60.8 | 62.4 |
| 256-bit vector instructions | Alternative Rust | 117.7 | 121.1 | 117.6 | 116.5 | 63.7 | 62.3 |
| 256-bit vector instructions | Assembly | 99.8 | 119.6 | 97.0 | 116.8 | 51.8 | 62.0 |
| 512-bit vector instructions | Default Rust | 116.0 | 118.5 | 115.5 | 116.9 | 60.4 | 62.2 |
| 512-bit vector instructions | Alternative Rust | 245.0 | 121.8 | 240.7 | 117.5 | 129.1 | 63.1 |
| 512-bit vector instructions | Assembly | 88.9 | 123.3 | 87.9 | 119.2 | 47.0 | 65.0 |
| Tuned for this Ryzen | Default Rust | 113.9 | 119.4 | 111.1 | 115.8 | 62.4 | 61.3 |
| Tuned for this Ryzen | Alternative Rust | 244.5 | 118.8 | 245.4 | 115.0 | 129.2 | 61.4 |
| Tuned for this Ryzen | Assembly | 86.8 | 120.1 | 86.0 | 117.6 | 46.1 | 61.0 |

The alternative Rust hashing backend was substantially slower with 512-bit
instructions and host-specific tuning in this run. Default Rust timings were
also slower in the build with extra CPU instructions. The causes of these
differences need investigation before drawing a performance recommendation.

### Ecrecover

The same builds measured evm2's recovery provider, including signature parsing,
public-key recovery, serialization and address hashing. Transaction dispatch
and calldata costs are excluded. `libsecp256k1` is the C backend; `k256` is
the Rust backend.

| Compilation setting | Hashing | C backend (µs) | Rust backend (µs) |
| --- | --- | ---: | ---: |
| Broad CPU support | Default Rust | 38.49 | 50.27 |
| Broad CPU support | Alternative Rust | 38.34 | 50.23 |
| Broad CPU support | Assembly | 38.26 | 50.38 |
| Extra CPU instructions | Default Rust | 38.16 | 49.88 |
| Extra CPU instructions | Alternative Rust | 38.18 | 49.97 |
| Extra CPU instructions | Assembly | 38.10 | 49.77 |
| 256-bit vector instructions | Default Rust | 38.37 | 49.59 |
| 256-bit vector instructions | Alternative Rust | 38.46 | 49.91 |
| 256-bit vector instructions | Assembly | 38.23 | 49.80 |
| 512-bit vector instructions | Default Rust | 38.26 | 49.99 |
| 512-bit vector instructions | Alternative Rust | 38.33 | 50.25 |
| 512-bit vector instructions | Assembly | 38.24 | 49.92 |
| Tuned for this Ryzen | Default Rust | 38.23 | 50.55 |
| Tuned for this Ryzen | Alternative Rust | 38.59 | 50.79 |
| Tuned for this Ryzen | Assembly | 38.12 | 50.41 |

These timings describe CPU work on this machine. Gas calibration also needs
cross-client and cross-hardware analysis.

## Benchmark against evm2

Earlier measurements and the gas-ratio methodology are in [BENCHMARKS.md](BENCHMARKS.md).

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
