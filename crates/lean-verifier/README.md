# lean-verifier

Independent, reference-derived verification of the pinned leanVM aggregate proof
protocol. This is a `no_std` + `alloc` library with Rust 1.90 support. Its only
normal dependency is the workspace's Alloy primitives; leanVM, its compiler and
its prover are development dependencies only.

This crate verifies existing aggregate proofs. It does not generate proofs or
replace the prover in `lean-aggregation`.

## Supported protocol

The protocol is pinned to leanVM revision
[`84780fb`](https://github.com/leanEthereum/leanVM/tree/84780fb42667bc288c0e567c125b7e10479fb568).
The dependency URL remains the workspace's existing mirror at that same revision.
Only that revision's fixed aggregation guest is accepted. The program length,
23-coordinate deferred point and program fingerprint are in `src/profile.rs`.
Changing any of these requires a new compatibility review and reference tests.

Verification includes:

- Strictly sorted, unique leanXMSS and leanSPHINCS `(public_key, message)` lists.
- Both list digests, optional LeanDA commitment and membership-challenge binding.
- Recomputed deferred bytecode evaluation, including recursive aggregates.
- The original transcript, binary fields, sumchecks, GKR, Merkle openings,
  grinding rules and WHIR polynomial commitment checks.
- Canonical reference proof encoding and complete proof consumption.

Claim lists travel separately from proof bytes. Reconstruct the expected keys,
message digests and DA commitment from application data before verification.
XMSS keys encode `merkle_root || public_param`; SPHINCS keys encode
`PK.seed || PK.root`. Each list sorts by these 32 bytes, then message bytes.
Both an empty list and `None` for DA have the reference's exact digest semantics.

## Preparing a verifier

The pinned program contains 8,388,608 little-endian `u64` words (64 MiB). Obtain
these words once, then call `Verifier::new(&words)`. It validates the shape, fixed
length and `Keccak(protocol_tag || program_words)` fingerprint before allocating
sparse evaluation tables. A different well-formed program is rejected too.
The prepared context does not retain the raw program and can be shared across
verifications; the caller can release its original words after preparation.

No generated 64 MiB binary is committed. To export the exact pinned program with
the reference compiler as an offline development step:

```sh
cargo +1.97.1 run -p lean-verifier --release --locked --example export_program -- /path/to/program.bin
```

The exporter refuses to overwrite an existing file and checks the program with
this verifier before writing. A consuming application must decode each eight-byte
chunk as a little-endian `u64`; do not reinterpret unaligned bytes as words.
Program preparation needs the full program plus the sparse tables temporarily.
This crate therefore needs an allocator and sufficient memory; compiling for an
embedded target does not imply the program fits that device.

```rust,no_run
use lean_verifier::{AggregateClaims, AggregateProof, B256, Verifier, VerifyError};

fn verify_received(
    program_words: &[u64],
    proof_bytes: &[u8],
    expected_key: B256,
    expected_message: B256,
) -> Result<(), VerifyError> {
    // Prepare once and retain this context when processing many proofs.
    let verifier = Verifier::new(program_words)?;
    let expected = AggregateClaims {
        lean_sphincs: vec![(expected_key, expected_message)],
        ..Default::default()
    };
    let proof = AggregateProof::from_bytes(proof_bytes)?;
    verifier.verify(&expected, &proof)
}
```

`from_bytes` only decodes; its success is never a verification verdict. Errors
distinguish program identity, encoding, claim order and invalid proofs without
exposing an unchecked execution path. The proof fields are private, so callers
cannot bypass decoder invariants by constructing an arbitrary execution object.

Applications must cap untrusted input bytes and claim counts before decoding or
building lists. The reference's Merkle phase/query/height/leaf caps are retained,
but this library does not choose application limits or provide recoverable OOM.
Message hashing, transaction domains and XMSS signing-state management belong to
the caller; this crate only verifies the given aggregate statement.

## Reference and adaptations

The execution verifier in `src/vm/` is a maintained port of
[`crates/verifier`](https://github.com/leanEthereum/leanVM/tree/84780fb42667bc288c0e567c125b7e10479fb568/crates/verifier),
not a clean-room implementation. The aggregate statement and deferred claim
follow the reference's `aggregation` crate. Original source SHA-256 digests and
revision are recorded in `reference.json`. Upstream MIT and Apache licenses are
included. The executable
[Lean verifier model](https://github.com/leanEthereum/leanVM/blob/84780fb42667bc288c0e567c125b7e10479fb568/formal/Statement/LeanVmVerifier.lean)
and
[aggregation statement](https://github.com/leanEthereum/leanVM/blob/84780fb42667bc288c0e567c125b7e10479fb568/formal/Statement/LeanVmGuest.lean)
are additional review references. EthLib's
[leanVM roadmap](https://github.com/ethereum/EthLib/blob/387788f72cfb084acc8f858690a105320b4d1f73/EthLib/Cryptography/LeanVm/README.md)
is not treated as a completed executable specification.

The port keeps arithmetic kernels, protocol constants and check order. Changes
are limited to `core`/`alloc`, crate-private visibility, the existing Alloy Keccak
interface for streamed program/statement hashing, Rust 1.90-compatible slice
conversion, and removal of prover reporting, unchecked replay and the unrelated standalone Keccak-proof API.
The reference Keccak permutation and one-shot Merkle hash kernel are retained; replacing the
short-message kernel with another backend measured slower on the validation host.
Program hashing streams words through a 1 KiB buffer rather than allocating a
second 64 MiB preimage. Statement hashing also streams its original encoding.
The zero-point deferred shortcut is the same as upstream and is covered by the
fixed program fingerprint and first-word conformance test.

There is no new formal correctness or security proof for this Rust port, and no
independent security audit. Compatibility tests establish agreement on a finite
corpus, not universal correctness. The pinned protocol's security assumptions
and parameter limitations still apply.

## Validation and benchmarks

Tests compare full verdicts with the pinned reference on rates 1 through 4,
recursive merge and pruning, both signature schemes, and a real DA commitment.
They also check program identity, encoding round trips, truncation, trailing
bytes, hostile size announcements, mutations, and changed/unsorted/duplicate
claims. Original arithmetic, hash and polynomial-check tests are retained.
The existing workspace CI includes this crate automatically; there is no separate
aggregation workflow.

```sh
cargo test -p lean-verifier --release --locked
cargo clippy -p lean-verifier --release --locked --all-targets --all-features -- -D warnings
cargo +1.90.0 check -p lean-verifier --locked --lib --no-default-features
cargo bench -p lean-verifier --locked --bench verify
cargo bench -p lean-verifier --locked --bench verify --features asm-keccak
```

The benchmark verifies the same leaf and recursive proofs with the same prepared
program and expected claims in both implementations. It measures full
verification, including deferred evaluation, with and without decoding. Program
preparation and proof generation are outside the timing loop. It alternates the
implementations and reports the median of five batches of 30 calls. Use identical
compiler/CPU flags and an otherwise idle machine when comparing results.

A validation run on Windows x86_64, Intel Core i5-1340P, Rust 1.97.1,
`RUSTFLAGS="-C target-cpu=native"`, with the workspace thin-LTO bench profile:

| Case | Default: local / reference (ms) | `asm-keccak`: local / reference (ms) |
| --- | --- | --- |
| Leaf verification | 10.521 / 10.521 | 10.230 / 10.236 |
| Leaf decoding + verification | 12.084 / 12.249 | 11.840 / 12.042 |
| Recursive verification | 16.545 / 16.592 | 16.292 / 16.527 |
| Recursive decoding + verification | 18.196 / 18.175 | 17.970 / 18.113 |

These small differences indicate approximate parity on this machine, not a
portable speedup. `asm-keccak` affects the Alloy streaming hashes; the VM's
reference Merkle and transcript kernels remain the same. Existing signing and
proving paths are unchanged.
