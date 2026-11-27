# SPHINCS source verification

This guide explains the correctness claim for `crates/lean-sphincs`, how it is
proved, and how to check the evidence. The scope is the SPHINCS crate. The
aggregation and independent VM-verifier crates have separate proof and
conformance gates described in the [formal overview](../README.md).

## What formal verification means

A formal proof establishes a precise mathematical statement, and a small proof
checker checks every reasoning step. Lean is both a language for expressing such
statements and a theorem prover whose kernel checks their proofs.

For this crate, the statement is functional refinement: the implementation's
observable result agrees with a specified mathematical algorithm. Charon extracts
the actual Rust bodies into its intermediate representation; Aeneas translates
those bodies into Lean functions. The proofs connect those functions to the
pinned EthLib algorithms and the explicit interface models below.

The difference from a test is the quantifier. A test might check that one saved
signature verifies. The roundtrip theorem covers every 32-byte seed and message
for which signing succeeds. It does not enumerate those inputs: it proves the
relationship symbolically.

For example, the established relationship has this shape:

```text
for every seed and message:
  if sign(seed, message) returns Ok(signature),
  then verify(key_gen(seed), message, signature) returns true
```

A separate contract describes failure. The private `sign_with_limit` helper with
limit zero returns `CounterExhausted { layer: 0 }`. For every other `u64` limit,
the proof describes the actual bounded search, exact first exhausted layer, or
exact successful signature bytes. Public `sign` invokes that helper with `2^32`
attempts. The proof never assumes that every seed/message has a successful
encoding search.

Verification is related to the reference decoder and verifier for every
signature byte slice. Rejected encodings produce `false`; accepted encodings
receive the same Boolean verdict as EthLib's `verifyWith`. This includes invalid
lengths and invalid layer encodings, rather than a premise that input bytes are
already a valid signature.

For a smaller concrete example, the checked [Keccak proof](../RustCrypto/Hash/Keccak/Permutation.lean)
contains this statement (the proof is in that source file):

```text
theorem chiElement_spec (rotated : State) (index : Usize)
    (hi : index.val < 25) :
    chiElement rotated index ⦃ out => out = chi rotated index.val ⦄
```

The arguments mean **every** state and machine-word index satisfying the bound,
not 25 saved test vectors. The `⦃ out => ... ⦄` contract requires a successful
result equal to the mathematical chi lane; the proof discharges the checked
array accesses and arithmetic. This is a proof-side helper. The theorem
`source_chi_eq_elements` ties its 25 calls to the actual translated Rust chi
helper. The array, round, full 24-round loop and public-API proofs then compose
that result, so an unrelated helper proof alone cannot establish source correctness.

## Is the crate fully verified and correct?

**The completed source proof covers the whole deterministic functional behavior
of the SPHINCS crate within its documented models, across all five production
configurations.** “Correct” here means that behavior matches those specifications;
it is not a claim of unconditional security or absence of every possible bug.

The complete source gate passed in all five configurations after the
module-directory reorganization, including the audits, corruption controls and
closing input-identity guards. The theorem bodies and Rust implementation are
unchanged; the fresh run checks the new imports and verification-tool paths.

The preceding performance-fix baseline was certified and commit-bound at
[`b82f2a78c6bb1c71ecc14f5ce247aeb7c1982c0a`](https://github.com/Soubhik-10/lean-crypto/commit/b82f2a78c6bb1c71ecc14f5ce247aeb7c1982c0a).
Its hosted [CodSpeed workflow](https://github.com/Soubhik-10/lean-crypto/actions/runs/45942099238)
also passed; benchmark success is separate from proof checking. Use the fresh
source certificate for the reorganized proof inputs: the baseline certificate
describes its own revision, not changed module paths. The evidence instructions
below explain how to bind a completed run to the intended Git commit.

The five configurations are scalar, SSE2, AVX2, SSE2 with assembly hashing, and
AVX2 with assembly hashing. Scalar is extracted for
`aarch64-unknown-linux-gnu`; x86 builds use their production SIMD and hashing
feature selections. These are the configurations in the source gate, rather than
a universal claim about every possible Rust compiler target or dependency build.

| Covered behavior | What the contracts establish |
| --- | --- |
| Public `key_gen` | Every typed 32-byte seed gives the canonical public seed, top-tree root and 32-byte public-key encoding. |
| Public `sign` and private bounded signer | Exact output or failure for every seed/message and every `u64` helper limit; default `2^32` trials, first successful counter, precise first exhausted layer, and retained counter-serialization semantics. |
| Public `verify` and decoding | Reference-equivalent verdict for every typed key/message and arbitrary signature bytes, including malformed lengths/encodings and root mismatches. |
| Serialization | Exact 7,740-byte signature layout, counter/chain/FORS/path order, reader/writer updates and lossless typed encoding/decoding. |
| Complete internal paths | FORS signing and all openings, WOTS+C chains/search/recovery, Merkle construction/climbing, every hypertree layer and cached top-tree path. |
| SIMD batching | Per-lane word arithmetic, all 24 Keccak rounds, 64/80-byte hashing, lane ordering, gathers/scatters, queues, windows and scalar tails. |
| Error methods | Extracted Display, Debug, Clone, equality and Error supertrait behavior under the observable formatting model. |
| Composition | Every signature successfully generated from a key is accepted by actual public verification, including exact byte decoding. |

EthLib supplies the reference verification and signing components. The complete
bounded signer is composed from its WOTS/FORS/Merkle primitives with the Rust
attempt limits, first-success/failure behavior and byte encoding. It does not
replace bounded search with an assumed successful unbounded search.

These contracts also retain failure/short-input branches in internal readers,
writers and tree helpers. Typed public APIs have their actual domains: public
keys and messages are fixed-size values, while verification accepts a byte slice.
There is no theorem about passing an invalid-length key to a Rust function whose
type cannot accept one.

## The trust boundary

The result depends on the following components and models:

| Boundary | Role |
| --- | --- |
| Lean kernel and standard foundations | Check the proofs. The dependency audit allows only `propext`, `Classical.choice` and `Quot.sound`. |
| Pinned Charon/Aeneas translation | Connect the extracted Rust bodies to the Lean functions being proved. The translator itself and Rust's compiler are not verified by these proofs. |
| Rust standard-library interface | Models operations used by the extracted crate, including arrays, slices, scalar arithmetic and the explicit formatting replacements. |
| Alloy Keccak interface | Models streaming hashing as hashing the accumulated byte stream with the pinned EthLib Keccak definition. This does not verify the dependency's Rust or assembly machine code. |
| `wide` interface | Models ordered lanes of 64-bit words and their operations. The source batching schedule and permutation are proved on top of this model. |
| Pinned EthLib specification | Defines the intended deterministic cryptographic operations and serialization; choosing the right specification remains a review obligation. |

The execution model is deterministic and uses Lean's `Id` boundary for the
cryptographic primitives. The proofs do **not** establish cryptographic hardness,
hash-query trace equivalence, constant time, side-channel resistance, Rust
compiler correctness, external dependency machine-code correctness, or CPU
correctness. In particular, functional output equality does not transfer the
older reference's random-permutation security theorem or query accounting to
Rust's different execution order.

The caller still supplies the seed and message digest and follows the scheme's
operational requirements. A functional proof does not generate entropy, enforce
a per-key signing budget, or validate an application's domain separation.

### Formatting and errors

The [observable standard-library model](../Runtime/README.md) captures formatting
arguments, options, writer state and partial output on failure. The formatting
proofs cover all byte-valued error layers, normal/alternate Debug and supported
writer/formatter behavior.

Width is represented by its effective numeric value. Absent width (`None`) and
explicit zero width (`Some 0`) render identically for the proved `SignError`
methods, so the model identifies those cases. This is an abstraction for those
methods, not an equality of the underlying Rust options or a claim about every
program that can inspect a formatter.

Rust's default `Error::source` body is not present in the extraction. It remains
a trusted standard-library boundary, without an extracted-source theorem here.
The observable model is documented against Rust 1.97.1 and the pinned extraction
compiler; it does not verify the standard library's unsafe implementation.

## How the proof is produced

```text
Pinned Rust source -> Charon extraction -> Aeneas Lean functions
                                                |
Pinned EthLib + explicit interface models -> kernel-checked source contracts
                                                |
                           dependency audit + corruption controls
                                                |
                           hashes and per-configuration evidence
```

1. **Pin and extract.** [`extractor.json`](../extractor.json) pins the tools and
   extraction compiler. The extractor records source hashes, tool identity and
   all five configurations. Local function bodies must be present and non-opaque.
2. **Translate.** Aeneas emits the actual Lean bodies. Translation metadata and
   generated-file hashes connect them to the recorded extraction run.
3. **Prove the contracts.** Lean checks component and whole-API proofs against
   those bodies and the reference. The complete SIMD loop, bounded signing,
   decoding and successful-signature composition are included.
4. **Audit and test rejection.** [`Audit/Source.lean`](../RustCrypto/Audit/Source.lean)
   requires the main theorems by name and audits transitive assumptions.
   Corruption controls must reject changed serialization, SIMD rotation/chi,
   injected assumptions and a missing required contract. The chi control rechecks
   the helper/round proof module against a typed mutated body; the ordinary gate
   independently checks every full 24-round and downstream contract.
5. **Record the exact inputs.** The gate verifies source/proof/tool/model identity
   before and after checking, then writes hashed evidence. A certificate belongs
   to those exact inputs, rather than every future revision of the repository.

AI assistance contributed to implementation and proof development. Proof
acceptance rests on the pinned pipeline, Lean kernel checks and recorded audits;
AI authorship is not evidence of correctness. Review of the statements and
trusted models remains necessary.

## Finding the proofs

The [formal directory overview](../README.md#directory-layout) lists the groups.
Useful entry points are:

| File/module | Stable theorem namespace and examples |
| --- | --- |
| [Keygen/KeyGen.lean](../RustCrypto/Keygen/KeyGen.lean) | `RustCrypto.KeyGen.key_gen_ethlib_spec` |
| [Signing/Full/Core.lean](../RustCrypto/Signing/Full/Core.lean) | `RustCrypto.FullSign.sign_with_limit_ethlib_spec`, `sign_ethlib_spec` |
| [Verification/Api.lean](../RustCrypto/Verification/Api.lean) and [Root](../RustCrypto/Verification/Root) | `RustCrypto.WholeVerifier.verify_*_ethlib_spec` and concrete backend contracts |
| [Serialization/Layout/Signature.lean](../RustCrypto/Serialization/Layout/Signature.lean) | `RustCrypto.Layout` byte-layout contracts |
| [Correctness/Signing](../RustCrypto/Correctness/Signing) | `RustCrypto.CanonicalCorrectness.sign_with_limit_roundtrip_*`, `sign_roundtrip_*` |
| [Hash/Keccak](../RustCrypto/Hash/Keccak) | `RustCrypto.Permutation` round/permutation contracts |
| [Formatting](../RustCrypto/Formatting) | `RustCrypto.ErrorFormatting` |
| [Audit/Source.lean](../RustCrypto/Audit/Source.lean) | Required declarations and the assumption allowlist |

Module names now follow the folders, while declaration namespaces remain stable.
For example, `import RustCrypto.Signing.Full.Core` makes the declarations in
namespace `RustCrypto.FullSign` available. The path organization changes where a
proof is imported, not the mathematical contract's name.

## Reproducing the source gate

Use Linux/WSL, Python 3 and a C toolchain. Keep runtime/build caches on native
Linux storage. The [source workflow](../../.github/workflows/sphincs-source.yml)
contains the complete clean setup, including source archives, OCaml/opam,
Charon's `rustc-dev`/`rust-src`/LLVM components, and the scalar target.

| Input | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.36.0` |
| Rust extraction compiler | `nightly-2026-09-17` |
| OCaml | `5.3.0` |
| Charon | `695be3d6292e988eedd8afcb7a709146a0ff4f01`, version `0.1.324` |
| Aeneas | `fb44cb400eb6bfe7dce97422ebe8fa748b7e4f9b` |
| EthLib | `ec1f398c9427e374160e68ce158a39e40805fd25`, with the file hashes in [ethlib.json](../ethlib.json) |

With the pinned binaries and Lean available on `PATH`, run from the repository
root. Set the active extraction toolchain explicitly; installing the nightly alone
does not select it for Charon:

```sh
set -euo pipefail
runtime=/absolute/path/to/sphincs-runtime
charon=/absolute/path/to/charon
aeneas=/absolute/path/to/aeneas
export RUSTUP_TOOLCHAIN=nightly-2026-09-17

python3 -I scripts/prepare_batching.py
(cd formal && lake build Batching +EthLib.Cryptography.Sphincs.Serialization)
python3 -I scripts/prepare_rust_runtime.py --runtime "$runtime" --stdlib-model
python3 -I -m unittest discover -s scripts -p test_translation.py

python3 -I scripts/extract_sphincs.py --charon "$charon" \
  --target-dir "$runtime/extraction-targets" | tee "$runtime/extraction.stdout"
extraction=$(tail -n 1 "$runtime/extraction.stdout")
python3 -I scripts/translate_sphincs.py --aeneas "$aeneas" \
  --extraction-run "$extraction" | tee "$runtime/translation.stdout"
report=$(tail -n 1 "$runtime/translation.stdout")
python3 -I scripts/check_sphincs_source.py --runtime "$runtime" \
  --translation-run "$(dirname "$report")" \
  --proof-workspace "$runtime/source-proof" --jobs 2
```

Charon's `--sysroot default` is supplied by the extraction script. Use the default
`--jobs 2` initially: proof workers can each require several GiB of memory.
Increasing parallelism does not strengthen a proof, and a killed/partial run
cannot produce a complete certificate. Extraction or translation success alone
is not proof success.

The [source workflow](../../.github/workflows/sphincs-source.yml) runs on relevant
pull requests, pushes to `main`, weekly and on manual dispatch. Its artifact keeps
extraction, translation, runtime-model and source-proof evidence. Older
security/finite-conformance checks run in a
[separate workflow](../../.github/workflows/formal.yml).

## Reading and checking the evidence

A successful run writes `formal/.cache/source-runs/<run>/evidence.json`. Important
fields are:

| Field | Meaning |
| --- | --- |
| `sources`, `proof_sources`, `pipeline_sources` | SHA-256 identities of the checked Rust/configuration, proof and pipeline inputs, with CRLF normalized to LF. |
| `variants` | All five configurations, generated-body identities, concrete proof modules, worker source snapshots and `kernel_checked: true`. |
| `stdlib_model`, `toolchain` | The explicit model manifest and pinned extraction/translation/checking tools. |
| `controls` | Which unchanged cases were accepted and corruptions were rejected. |
| `translation_report_sha256` | Identity of the translation report used by the proof run. |
| `scope`, `trust_boundary`, `not_proved` | The claim and its explicit limits. |

The `full_crate_formally_verified` flag is the pipeline's summary of this
functional claim. Reading that Boolean is not a replacement for verifying the
run, its complete configuration set and input identities. Hashes bind content;
they do not authenticate an arbitrary JSON file or themselves prove a theorem.
Use evidence from the trusted CI run or a locally reproduced gate.

For an exported bundle with `SHA256SUMS`, first run `sha256sum -c SHA256SUMS` in
that bundle. Then return to the repository checkout and compare the certificate's
inputs to the intended Git commit. Run the following Python command from that
checkout so `git show` reads the intended repository. It accepts either the
original `evidence.json` or an identical exported copy named
`source-verification.json`:

```sh
python3 - /path/to/evidence.json FULL_COMMIT_SHA <<'PY'
import hashlib, json, re, subprocess, sys
report = json.load(open(sys.argv[1], encoding="utf-8"))
commit = sys.argv[2]
assert re.fullmatch(r"[0-9a-f]{40}", commit)
assert report["full_crate_formally_verified"]
assert report["source_functional_refinement_complete"]
variants = report["variants"]
assert len(variants) == 5
assert {v["variant"] for v in variants} == {
    "scalar", "sse2", "avx2", "sse2-asm", "avx2-asm"}
assert all(v["kernel_checked"] is True for v in variants)
for group in ("sources", "proof_sources", "pipeline_sources"):
    for path, expected in report[group].items():
        blob = subprocess.check_output(["git", "show", f"{commit}:{path}"])
        actual = hashlib.sha256(blob.replace(b"\r\n", b"\n")).hexdigest()
        assert actual == expected, (group, path)
print("All certified Git inputs match", commit)
PY
```

The working tree may contain later edits even when a historic commit matches.
Source or proof changes, changed external models, module-import changes or tool
pin changes require a fresh complete five-configuration proof run. Tests,
benchmarks, and the earlier Lean-description equivalences remain useful separate
evidence; none substitutes for that run.

## Generated files and maintenance

`formal/.cache`, `.lake/build` and native runtime/Cargo targets are generated,
ignored build/download locations. They contain pinned dependency copies,
translations, compiled proofs and run data; they are not the maintained proof
sources. Export a completed certificate, its extraction/translation/model
manifests and any needed logs before clearing those caches.

Maintain the source proofs under `RustCrypto/`, their explicit models under
`Runtime/`/`RustCrypto/Models/`, and the pins beside this guide's parent directory.
Change the specification or trust boundary deliberately, and check that the
resulting theorem still describes the intended public behavior.
