# lean-sphincs

A Rust workspace for post-quantum signatures and aggregation, with Alloy types.
Both crates support `no_std`; aggregation claim lists use `alloc`. The default
`std` feature enables reference proof generation and verification.

| Crate | Description |
| --- | --- |
| [lean-sphincs](crates/lean-sphincs) | leanSPHINCS key generation, deterministic signing and verification without heap allocation |
| [lean-aggregation](crates/lean-aggregation) | leanSPHINCS proof aggregation and verification through the pinned leanVM backend |

See the [crate README](crates/lean-sphincs/README.md) for its API,
parameters, features and validation guarantees.

The `no_std` workspace supports Rust 1.90. Reference proof generation and
verification require `std` and Rust 1.97.1 for the pinned backend.

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
