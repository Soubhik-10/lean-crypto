# lean-sphincs

A Rust workspace for post-quantum signatures and aggregation, with Alloy types.
All three crates support `no_std`; aggregation claims and the independent
verifier use `alloc`. The `lean-aggregation` default `std` feature enables
reference proof generation and verification.

| Crate | Description |
| --- | --- |
| [lean-sphincs](crates/lean-sphincs) | leanSPHINCS key generation, deterministic signing and verification without heap allocation |
| [lean-aggregation](crates/lean-aggregation) | leanSPHINCS proof aggregation and verification through the pinned leanVM backend |
| [lean-verifier](crates/lean-verifier) | Independent, reference-derived `no_std` verification of the pinned leanVM aggregate protocol |

See the [crate README](crates/lean-sphincs/README.md) for its API,
parameters, features and validation guarantees.

The `no_std` workspace supports Rust 1.90. The `lean-aggregation` reference
backend requires `std` and Rust 1.97.1. The independent `lean-verifier` needs
prepared, fingerprint-checked program data; see its [README](crates/lean-verifier/README.md)
for setup, compatibility and validation limits.

## Formal verification

The `lean-sphincs` crate includes Lean proofs relating its extracted Rust source
to a pinned EthLib specification. The completed five-configuration source audit
covers key generation, signing and counter exhaustion, decoding/verification,
serialization, SIMD batching and successful-signature roundtrips for all inputs
within the documented models.

This is a functional-correctness claim with explicit translation,
standard-library, hashing and SIMD assumptions. Cryptographic security, constant
time and compiled machine-code correctness are outside its scope. Read
[what is verified, the current certified revision, and how to reproduce it](formal/docs/verification.md).
The [formal overview](formal/README.md) also describes the separate upstream
security/conformance and aggregate-verifier gates.

## Benchmarks

AMD Ryzen 9 8940HX, Linux/WSL2, Rust 1.97.1, native CPU flags,
`asm-keccak`, thin LTO, one codegen unit and logical CPU 8; measured 23 November 2026.

| Workload | This workspace | Pinned leanVM reference | Speedup |
| --- | ---: | ---: | ---: |
| leanSPHINCS verification | 38.56 µs | 128.86 µs | 3.34x |
| leanSPHINCS signing | 93.23 ms | 127.25 ms | 1.36x |
| leanSPHINCS key generation | 48.68 ms | 66.28 ms | 1.36x |
| Aggregate leaf: decode + verify | 10.432 ms | 14.256 ms | 1.37x |
| Aggregate recursive: decode + verify | 14.951 ms | 20.017 ms | 1.34x |

Both campaigns use three fresh processes. Signature results retain 132 samples
per operation over 11 shared fixtures; aggregate results retain 450 paired calls
per workload/backend, summarized as medians of round means. The aggregate leaf
contains two signatures; its recursive parent retains one claim, at log-inverse-rate 1.
Preparation and proving are outside the timer. Native evm2 ecrecover measured
26.69 µs in the signature campaign. These are host-specific CPU timings.

```sh
bash benchmarks/compare.sh native --cpu 8 --cc clang --session benchmarks/results/signatures
bash benchmarks/compare.sh verifier --cpu 8 --session benchmarks/results/verifier
```

[Full setup and raw results](benchmarks/README.md),
[verifier default/assembly results](crates/lean-verifier/README.md#validation-and-benchmarks),
and [benchmark commands](benchmarks/SUITE.md).

## Development

```sh
cargo test --workspace --release --locked
cargo test --workspace --release --locked --all-features
cargo test --workspace --release --locked --no-default-features
cargo +1.90.0 check --workspace --locked --lib --no-default-features
cargo clippy --workspace --all-targets --all-features --locked -- -D warnings
cargo doc --workspace --no-deps --all-features --locked
cargo fmt --all -- --check
```

Crates live under `crates/` and share package metadata, dependency versions and
lints from the root `Cargo.toml`. To add a crate, put its package in
`crates/<name>/`, inherit the applicable workspace settings, and add an entry
to the table above.

The differential-test runner, fuzz targets and benchmark adapters are separate,
unpublished tool packages. Their dependencies and lockfiles stay isolated from
the library workspace.

## Resources

- [Scheme and implementation guide](docs/guide.md)
- [Lean proofs and conformance CI](formal/README.md)
- [Differential tests](testing/README.md) and [fuzzing](fuzz/README.md)
- [Rust benchmark results and setup](benchmarks/README.md)
- [Batching and performance](benchmarks/BATCHING.md)
- [Shell benchmark commands](benchmarks/SUITE.md#compare-ours-leanvm-and-ecrecover)

## License

MIT OR Apache-2.0 for the implementation. EthLib-derived test data is CC0-1.0.
