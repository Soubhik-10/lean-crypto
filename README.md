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

**The SPHINCS crate has completed deterministic source functional verification
under documented models in five production configurations. The entire workspace
is not formally verified, and this is not an unconditional cryptographic-security
claim.**

The source and proof inputs at
[`ce0a851`](https://github.com/Soubhik-10/lean-crypto/commit/ce0a851ab1a1a989e1c26fd2401ef0f12af22bfc)
passed fresh extraction, translation and the complete Lean source gate locally
and in [hosted CI](https://github.com/Soubhik-10/lean-crypto/actions/runs/45950180717).
That run checks scalar, SSE2, AVX2, SSE2 with assembly hashing, and AVX2 with
assembly hashing. Scalar is extracted for `aarch64-unknown-linux-gnu`; this is not
a claim about every possible compiler target or dependency configuration.

### What formal verification means here

A test checks particular inputs. A formal proof establishes a precise statement
for every input in its stated domain, and Lean's kernel checks the proof.
Our statement is **functional refinement**: the Rust implementation's observable
results agree with the specified mathematical algorithms, including failure.

This proof starts from the actual Rust function bodies, rather than only a
separately written Lean model:

```text
Pinned Rust source -> Charon extraction -> Aeneas-generated Lean functions
                                                   |
Pinned EthLib specification + interface models -> Lean source contracts
                                                   |
                            Kernel checks, assumption audits and evidence
```

Charon extracts the Rust bodies into an intermediate representation. Aeneas
translates them into Lean functions. Component proofs connect those translated
functions to the pinned EthLib specification; whole-API proofs compose those
results. The translation and the external interface models remain trusted parts
of that connection. Alloy streaming hashes are modeled as hashing the
accumulated bytes with EthLib Keccak; `wide` operations are modeled as ordered
64-bit lanes. The proofs establish the crate behavior on top of those models.

### Exactly what the SPHINCS proofs cover

| Behavior | Established result |
| --- | --- |
| Key generation | Every typed 32-byte seed produces the canonical public seed, top-tree root and public-key bytes. |
| Signing and failure | Public `sign` and the private `sign_with_limit` helper return the specified signature bytes or exact counter-exhaustion error. The helper is covered for every `u64` limit; public signing uses `2^32` attempts. |
| Decoding and verification | Public verification agrees with the reference decoder and verifier for every signature byte slice, including malformed lengths, invalid encodings and root mismatches. |
| Serialization | Exact public-key and 7,740-byte signature layouts, field order, reader/writer updates and lossless typed encoding/decoding. |
| Internal paths | Complete FORS openings, WOTS+C search/chains/recovery, Merkle construction/climbing, every hypertree layer and cached top-tree paths. |
| SIMD batching | Ordered word lanes, all 24 source Keccak rounds, 64/80-byte hashing, gathers/scatters, queues, windows and scalar tails. Dependency implementations are covered by interface models, as explained below. |
| Error methods | Extracted `SignError` Display, Debug, Clone, equality and Error supertrait behavior under the observable formatting model. The default `Error::source` body is a trusted boundary. |
| End-to-end functional composition | Every successfully generated signature is accepted by public verification with the corresponding generated public key. |

For example, the roundtrip theorem has this shape:

```text
for every typed seed and message:
  if sign(seed, message) returns Ok(signature),
  then verify(key_gen(seed), message, signature) returns true
```

The condition matters: signing performs a bounded search. We prove both its
success and failure behavior, not that every seed/message must produce a
signature. For example, the private helper with a zero attempt limit returns
`CounterExhausted { layer: 0 }`. Public verification is proved for arbitrary
signature bytes; it does not assume that incoming bytes already encode a valid
signature. Key and message inputs retain their actual fixed-size Rust types.

### How we checked it

1. **Pin and extract the inputs.** The extraction compiler, Charon, Aeneas,
   Lean and EthLib revisions are pinned. Each of the five configurations gets
   its own extraction. The gate checks that local Rust function bodies are
   present and non-opaque, and records their source and generated-file hashes.
2. **Prove components and compose the APIs.** Lean checks the translated
   arithmetic, memory accesses, serialization, complete SIMD permutation,
   signing/search, decoding and verification contracts. These feed the actual
   key-generation/signing/verification roundtrip proofs.
3. **Audit the proof dependencies.** The audit requires the principal theorems
   by name and checks their transitive assumptions. Only Lean's standard
   foundations, `propext`, `Classical.choice` and `Quot.sound`, are allowed;
   injected assumptions or missing required contracts fail the gate.
4. **Check that corruption is rejected.** Negative controls exercise changed
   serialization, incorrect SIMD rotation/chi, injected assumptions and missing
   contracts. These controls complement the ordinary complete proofs; their
   precise scope is recorded in the evidence and the detailed guide.
5. **Bind the result to the checked files.** The gate checks input identity
   before and after proof checking and writes per-configuration evidence with
   source, proof, pipeline, tool and model identities. Extraction or translation
   success alone does not count as proof success.

The main theorem entry points and exact tool pins are in the
[verification guide](formal/docs/verification.md#finding-the-proofs). Its
[reproduction instructions](formal/docs/verification.md#reproducing-the-source-gate)
include the complete Linux/WSL command sequence, and its
[evidence instructions](formal/docs/verification.md#reading-and-checking-the-evidence)
show how to check a certificate against the intended Git commit. The
`full_crate_formally_verified` report field summarizes this documented functional
scope; it does not expand it to the whole workspace or every security property.

The [source workflow](.github/workflows/sphincs-source.yml) repeats the gate on
relevant pull requests, relevant pushes to `main`, weekly and on manual dispatch.
Changes to source, proofs, imports, models or tool pins require a fresh complete
run. The earlier security/model proofs and finite Rust-versus-Lean comparisons
run in a [separate workflow](.github/workflows/formal.yml). Tests and fuzzing
provide additional evidence but do not replace the universal source proofs.

AI assistance contributed to implementation and proof development. Acceptance
rests on the pinned pipeline, Lean kernel checks and recorded audits. AI
authorship does not establish correctness; the specifications and trusted models
still need review.

### What remains outside the completed proof

| Area | Remaining gap or assumption |
| --- | --- |
| Cryptographic security transfer | The upstream strong-unforgeability result concerns its mathematical scheme in the random-permutation model, under stated assumptions and query bounds. We have not proved hash-query trace equivalence or transferred that security bound to Rust's different execution order and batching schedule. Functional output equality alone does not establish that transfer or concrete Keccak hardness. |
| Aggregation and LeanVM | `lean-aggregation` and `lean-verifier` have separate model proofs and conformance checks, not a complete Rust-source refinement proof. The SPHINCS proof does not verify the whole aggregation system, VM prover or VM verifier. |
| Side channels and secret handling | Constant-time execution, timing/memory-access leakage and broader secret-handling properties have not been proved. |
| External dependencies and translation | The pinned Charon/Aeneas translation and documented Rust standard-library, Alloy Keccak and `wide` interface models are trusted. We do not prove those dependencies' complete implementations, unsafe internals or assembly machine code. Rust's default `Error::source` body is not extracted. |
| Compiler and hardware | Rust/LLVM code generation and CPU correctness are outside these source proofs. |
| Application requirements | Callers supply entropy and message digests and must enforce applicable signing budgets and domain separation. The functional proofs do not establish those application-level obligations. |

For clarity, the workspace currently has these distinct levels of assurance:

| Crate | Verification status |
| --- | --- |
| `lean-sphincs` | Complete deterministic source functional refinement in the five configurations above, under the stated models and trust boundary. |
| `lean-aggregation` | Pinned LeanVM backend and reference conformance tests; no complete Rust-source correctness proof. |
| `lean-verifier` | Pinned protocol and wire-model theorems plus finite Rust conformance tests; no complete proof that the Rust port implements that model for all inputs. |

See the [trust-boundary discussion](formal/docs/verification.md#the-trust-boundary),
[formal overview](formal/README.md) and
[independent verifier's limits](crates/lean-verifier/README.md#reference-and-adaptations)
for the exact assumptions and separate security/model/conformance claims.

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
