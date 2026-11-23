# lean-aggregation

A leanSPHINCS aggregation adapter with Alloy keys and message digests. Native
signature admission uses this workspace's `lean-sphincs`; proof generation and
complete aggregate verification use [leanVM at
`84780fb42667bc288c0e567c125b7e10479fb568`](https://github.com/Rimeeeeee/leanVM/tree/84780fb42667bc288c0e567c125b7e10479fb568).

This is an adapter around the reference backend, not a new proof system. It
preserves the backend's proof bytes, statement construction, fixed aggregation
program, transcript and deferred bytecode verification. The reference's leanXMSS
claim list is empty and its DA commitment is absent. Transaction parsing,
dependency digests, wrapper transport and consensus policy belong to the caller.

Disable default features for a `no_std + alloc` claim-set API without leanVM.
The default `std` feature enables reference proof generation and verification.

## Use

```rust,no_run
use lean_aggregation::{Aggregate, Aggregator, B256, Claims, setup};
use lean_sphincs::{key_gen, sign};

// Once at process startup. Zero lets the reference choose its thread count.
setup(0);

// Example only: production seeds must contain 32 uniformly random secret bytes.
let seed = B256::repeat_byte(7);
let public_key = key_gen(&seed);
let message = B256::repeat_byte(1);
let signature = sign(&seed, &message)?;
let expected = Claims::new([(public_key, message)]);

let mut inputs = Aggregator::with_capacity(1);
inputs.add_signature(&public_key, &message, signature.as_slice())?;
let leaf = inputs.prove(None, 1)?;
assert!(leaf.verify(&expected));

// At the receiver, reconstruct expected claims independently from transactions.
let received = Aggregate::from_bytes(expected.clone(), &leaf.to_bytes())?;

// Retain exactly the requested claims, without the original signatures.
let mut parent = Aggregator::default();
parent.add_child(received)?;
let root = parent.prove(Some(&expected), 1)?;
assert!(root.verify(&expected));
# Ok::<(), Box<dyn std::error::Error>>(())
```

`Claims::new` sorts and deduplicates `(public_key, message)` pairs. Public keys
are `PK.seed || PK.root`, and messages are exact 32-byte digests. It does not
hash transactions or choose a signing domain. Proofs establish the exact
canonical claim set, not a superset.

`Aggregate::from_bytes` both decodes and verifies. It checks the complete
reference aggregate, including the deferred bytecode claim, before returning an
object that can be added as a child. A sender's claim list must not be treated
as the expected transaction obligations. The proof encoding carries no claims.

Use `Aggregator::with_capacity(count)` when the number of fresh signatures is
known, so the raw-input vector is allocated at its final size. Fresh signatures
are verified once with the native implementation when added. Invalid signatures
leave the aggregator unchanged. Child admission moves owned proof and claim
buffers; it neither clones them nor repeats native verification. The reference
guest still checks the witnesses cryptographically during proving.
`Aggregate::clone` is an explicit deep copy; prefer moving children when their
old owners no longer need them.

Each node accepts at most `MAX_RECURSIONS` children. To combine more, prove
intermediate nodes and add those results to a parent. `prove(None, rate)`
publishes the union; `prove(Some(&claims), rate)` publishes exactly the selected
covered claims. Uncovered claims and empty output are rejected by the backend.
An empty application dependency set should use the application's empty-proof
convention rather than requesting a proof of no claims.

Proving is blocking, uses the reference's process-wide thread pool and can
consume substantial memory. Concurrent proving calls serialize in the backend.
Call `setup` consistently before proving; changing an already running pool's
thread count panics, as in the reference. Bound untrusted signature counts and
proof byte lengths before using this API. This library does not impose a
network's proof-size or dependency-count policy.

## Features and toolchains

- The default `std` feature enables `Aggregate`, `Aggregator`, proof errors,
  backend limits and `setup`, selecting the reference stable prover.
- With `default-features = false`, `Claims` and `B256` remain available in
  `no_std + alloc` environments. leanVM is not built in this mode. An allocator
  must be provided by applications that construct nonempty claim lists.
- `experimental-prover` enables `std` and selects the pinned experimental
  prover, using the same proof protocol. Enable this feature to match the
  experimental backend used by the EIP-8288 devnet integration.
- `asm-keccak` forwards to `lean-sphincs` for native signature admission. It
  does not replace the prover's Keccak implementation.

The workspace's Rust 1.90 minimum applies to native signatures and the `no_std`
claim-set API. Proof generation and aggregate-proof verification require `std`
and Rust 1.97.1 because the pinned backend uses the standard library. They are
not available in `no_std` mode; no alternate proof verifier is substituted.

Both configurations expose the same sorted, deduplicated public claim pairs.
With `std`, claims retain the reference's native representation so proof
verification does not allocate or convert a second claim list. Feature selection
is performed at compile time and adds no runtime dispatch to the proof path.

This crate is consumed through Git because it depends on a pinned Git backend.
The separate `lean-sphincs` crate retains its allocation-free API and `no_std`
support. No native verification optimization is claimed to accelerate proving
by itself.

## Validation

```sh
cargo test -p lean-aggregation --release --locked
cargo test --workspace --release --locked --no-default-features
cargo +1.90.0 check --workspace --locked --lib --no-default-features
cargo check --workspace --locked --lib --no-default-features --target thumbv7em-none-eabi
cargo test -p lean-aggregation --release --locked --features experimental-prover,asm-keccak
cargo clippy -p lean-aggregation --release --locked --all-targets --all-features -- -D warnings
cargo doc -p lean-aggregation --locked --no-deps --all-features
```

The integration test compares generated proof bytes with a direct call to the
pinned reference and checks interoperability in both directions. It also covers
exact claim binding, signature and proof mutations, malformed encodings,
overlapping children, mixed raw and recursive inputs, recursive pruning without
original signatures, uncovered claims and the child limit. It runs against
either prover selected by the feature flag. Separate claim-set tests run with
and without `std`, checking identical ordering across public-key and message
byte boundaries. CI checks the entire `no_std` workspace on ARM Cortex-M and
at Rust 1.90, in addition to the default and experimental proof configurations.

The workspace's Lean proofs and Rust-to-Lean signature conformance evidence
remain scoped to `lean-sphincs`. They do not establish a formal proof of this
adapter or end-to-end recursive composition. This crate inherits the reference
backend's experimental status and security assumptions.

## Performance comparison

```sh
cargo bench -p lean-aggregation --locked --bench adapter --features experimental-prover,asm-keccak
cargo bench -p lean-aggregation --locked --bench adapter --features experimental-prover,asm-keccak -- --prove
```

The benchmark black-boxes its inputs, warms both paths, pairs adjacent adapter
and direct-reference calls in alternating order, and reports their separate
medians across five rounds. It compares matched native signature admission and
conversion, aggregate verification, and proof decoding plus full verification.
`--prove` additionally compares admission plus leaf proving. Both sides reserve
one raw-input slot and use the same native verifier, raw signature, four backend
threads, code rate and selected prover; process setup and signing are outside
the measurements. Run with matching compiler and CPU flags when comparing
results across machines.

The adapter does not serialize proofs between in-process aggregation steps or
reverify checked children on admission. Expected claim sets are prepared once,
so repeated verification does not allocate a second list in the adapter. The
benchmark includes the native admission work on both sides rather than comparing
checked adapter input with unchecked reference input.

### Local measurements

Intel Core i5-1340P, Windows x86-64 MSVC, Rust 1.97.1, `RUSTFLAGS="-C
target-cpu=native"`, `asm-keccak`, four prover threads and `log_inv_rate = 1`.
The bench profile uses the workspace's thin LTO and one codegen unit. These are
per-operation medians from five rounds of adjacent alternating calls, using one
signature claim. They do not establish performance for large claim sets or other
machines.

With `experimental-prover`:

| Operation | Adapter | Direct reference with the same native admission | Adapter / reference |
| --- | ---: | ---: | ---: |
| Native admission and input conversion | 87.139 us | 86.468 us | 1.0078 |
| Aggregate verification | 10.603 ms | 10.652 ms | 0.9954 |
| Decode and verify | 12.092 ms | 12.028 ms | 1.0053 |
| Native admission and leaf proving | 115.140 ms | 115.404 ms | 0.9977 |

With the default stable prover:

| Operation | Adapter | Direct reference with the same native admission | Adapter / reference |
| --- | ---: | ---: | ---: |
| Native admission and input conversion | 87.681 us | 87.093 us | 1.0067 |
| Aggregate verification | 11.074 ms | 11.063 ms | 1.0010 |
| Decode and verify | 12.651 ms | 12.398 ms | 1.0204 |
| Native admission and leaf proving | 140.863 ms | 146.103 ms | 0.9641 |

The observed differences are small and are not evidence of a backend speedup.
The adapter's proof operations delegate to the same implementation. Admission
reserves the known input count to avoid extra vector growth. Timings on this
hybrid-core machine varied between runs; these measurements are a local overhead
check, not a throughput guarantee.

## License

MIT OR Apache-2.0 for the adapter. The pinned leanVM crates are separate
dependencies under their upstream licensing terms.
