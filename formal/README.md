# Lean proofs, Lean equivalences and Rust conformance

The sections above the source-verification guide describe earlier upstream security,
Lean-model and finite-conformance work. The [production source contracts](#production-sphincs-source-verification)
below use a separate EthLib reference and gate.

The reference is [leanEthereum/leanVM at the immutable revision in upstream.json](https://github.com/leanEthereum/leanVM/tree/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/formal), using Lean 4.36.0. It credits [Verified-zkEVM/leanerVM](https://github.com/Verified-zkEVM/leanerVM) for its vendored formalization. CI fetches its source and licenses into an ignored cache. Our additional modules are in [Implementation](Implementation); `prepare_formal.py` copies them into that build and adds Lake targets, leaving the pinned upstream Lean definitions unchanged. Provenance artifacts include our source hashes.

## Three distinct claims

| Evidence | What is established | What is not established |
| --- | --- | --- |
| Upstream security theorem | `Sphincs.leanSphincsStronglyUnforgeable` proves the statement's scheme strongly unforgeable in the random-permutation model, under the stated signature limit, cryptographic assumptions and query accounting. | Security of every execution of this Rust library with concrete Keccak. |
| Lean-to-Lean proofs | Upstream connects crate-shaped Lean algorithms to its security model. Our kernel-checked lemmas connect selected Rust-shaped Lean descriptions to that statement, including failure. | Source refinement from those older models alone, or correctness of compiled machine instructions; see the separate source contracts below. |
| Production Rust-to-Lean comparisons | Actual Rust public-key bytes, deterministic signature bytes, verification/rejection results and component outputs agree with compiled Lean on the saved finite corpus. | Universal equivalence, signing success for every key/message, or automatic transfer of a security bound. |

### Upstream proof route

Read `formal/Statement/LeanSphincs.lean`, `formal/lean_sphincs/Sphincs.lean` and `formal/lean_sphincs/FORS/Crate.lean` at the pin. The crate-shaped Lean copy is a description of upstream's crate, not a transcription of this repository's optimized Rust.

* `FORS/CrateStatic.lean`: `FORS.Crate.eval_keygen` and `eval_sign` relate the crate-shaped algorithms to `FORS.Seeded` under every fixed hash answer function. Signing returns an `Option`; exhaustion is retained.
* `Sphincs/CrateSim.lean`: `Sphincs.Model.simulateQ_crateKeygen` and `simulateQ_crateSign` connect the crate-shaped Lean copy to the statement through explicit key/signature maps and a hash-over-permutation simulation. `Sphincs.Model.simulateQ_verify` connects verification.
* `FORS/CrateShort.lean`, `Sphincs/Queries.lean`, `Sphincs/ModelRpm.lean` and `Sphincs/AdvRpm.lean` supply the additional short-query, static-swap, worst-case cost and adversary-budget arguments needed for the security transfer. Output equality alone is not their justification.

Our Rust signer hashes the public-seed derivation before the PRF-key derivation, while the pinned description uses the reverse order. Rust also builds lower trees with a streaming stack and batches independent verification hashes. We do **not** extend the upstream security bound to these execution orders. The new schedule lemmas use a fixed, stateless permutation (`Id`); they are functional results and assert no stateful-oracle simulation, cost bound or security-game equality for Rust.

### Additional Lean theorems

[Implementation/Algorithms.lean](Implementation/Algorithms.lean) proves:

* `indexBefore_eq` and `layer_indices`: the successive divisions in the verifier's 8/8/10-bit index loop give the statement's leaf/tree indices for every 26-bit index and all three layers. Rust's shared, inlined `take_layer` helper is used by signing, verification and the boundary exporter. The source-derived `RustIndex` contracts below now prove its machine-word quotient/remainder behavior at every production layer height; the complete source callers are covered by the source contracts below.
* `scheduledEnds_eq_walkChain` and `scheduledEnds_eq_recoverChain`: three step-major WOTS passes give the statement's chain-major recovery for every digit, initial value and lane count, instantiated with its addressed hash under a fixed permutation. Original chain order is preserved. These prove the mathematical schedule, not the implementation of the SIMD primitive, buffering, scatter operations or scalar-tail loops.
* `search_none_iff`, `search_some_spec` and `search_counter_no_wrap`: bounded counter search fails exactly when every attempted encoding fails; success gives the least accepted counter in range, and at the actual `2^32` production limit that counter cannot wrap a 32-bit word.
* `search_eq_otsSignFrom`: that bounded search followed by chain opening equals the pinned statement's entire WOTS signer for every attempt budget and start counter, including failure. It does not assume signing succeeds. These older lemmas do not themselves prove whole-signature failure propagation, streaming tree construction or byte serialization.

`Implementation/Axioms.lean` inspects every theorem in the new namespace and rejects dependencies beyond `propext`, `Classical.choice` and `Quot.sound`. The inventory requires each of the eight documented declarations by name and verifies that it is a theorem; generated equation or auxiliary lemmas cannot replace a missing required theorem. Upstream's escape scanner also checks all of our Lean files. Kernel-skipping options, proof holes and native-decision proof shortcuts are forbidden.

## Conformance corpus and strict comparisons

The public-API exporter calls the real `key_gen`, `sign` and `verify`. It retains all 35 pinned cases and reproducible generated keys/messages. Mutations cover both sides of every serialized node boundary, each layer's counter/chain/path boundaries, key/message changes, truncation at field boundaries and trailing data. `FORMAL_CASES` accepts 1..16 generated pairs; `FORMAL_SEED` is a nonzero hexadecimal u64. CI derives the seed from the tested commit, so every backend receives identical inputs.

The ignored unit-test exporter in `crates/lean-sphincs/src/formal_tests.rs` is compiled only for tests, alongside the production modules. It directly calls production digest, decoder, WOTS recovery/signing, FORS recovery and Merkle climbing code. It adds:

* index boundaries around 8, 16 and 26 bits; codeword sums 127/128/129 and every digit position;
* layer counter values 0/1/255/256/65535/65536/`u32::MAX`, least-counter success and failure budgets 0/1/first/first+1/`2^32`;
* accepted WOTS encodings covering digits 0..3 and every scalar-tail length 0..3 in the 16-chain AVX2 window, with coverage assertions;
* zero/max/alternating FORS leaves, all 24 openings (checking SIMD lane/serialization order), and Merkle position/height boundaries.

`signature-kat` is built from the unchanged pinned CLI and statement. Our `implementation-kat` imports an exact prefix of the pinned CLI, excluding only its global entry point, to reuse its parsing/encoding helpers and compiler-replacement proofs and computes component answers with the **same pinned Lean algorithms**, not a second Rust reference. Both executables are built from the same source tree and toolchain as the checked proofs. The new executable's output formatting/parser is trusted test infrastructure; it is scanned for proof escapes but not itself a parser-correctness theorem.

Malformed signature lengths must first be rejected by Rust. The exporter then records `null` to match the Lean byte parser's `none`. Public-key/message lengths are fixed by Rust's types; invalid typed inputs are parser cases, not executions of a nonexistent Rust byte API. Exact-size invalid signatures compare the actual Boolean verdict. The real `2^32`-attempt exhaustion path is not exhaustively executed by this finite conformance gate. The source contracts below prove bounded exhaustion without executing every trial.

`run_formal.py` requires both manifests, every operation, exact files/results, no duplicate/unexpected/missing/skipped cases, successful process exits and a complete zero-mismatch summary. Eight regression tests protect these rules. Every matrix job also runs `check_formal_rejection.py`, which feeds deliberately wrong expected outputs to **both real Lean executables** and requires rejection. Corpora, build configuration, seeds, logs, source pin, source hashes and dependency reports are saved for replay.

## CI and reproduction

The existing [formal workflow](../.github/workflows/formal.yml) builds `Sphincs`, `FORS`, `FORS.Axioms`, `signature-kat`, `Implementation`, `Implementation.Axioms` and `implementation-kat` with the kernel enabled. It independently checks the upstream end statements' exact axiom footprints and every additional theorem's allowed dependencies. Comparisons and negative controls run in all four SSE2/AVX2 × RustCrypto/assembly configurations. Normal Rust builds contain none of the component export machinery and gain no trace hooks or public API.

Use Linux/WSL, Rust 1.97.1, Python 3, a C toolchain and the pinned Lean toolchain. Make the existing pinned source tree available at `formal/.cache/leanVM` (the workflow does this checkout), without running `lake update`. From this repository:

```sh
python3 scripts/prepare_formal.py
cd formal/.cache/leanVM/formal/lean_sphincs
lake exe cache get
python3 -I ../tools/escape-scan.py ../Statement ../common .
python3 -I ../lake-build.py . Sphincs FORS FORS.Axioms signature-kat \
  Implementation Implementation.Axioms implementation-kat
lake env lean -DwarningAsError=true Implementation/Axioms.lean
cd ../../../../..
export RUSTFLAGS='-C target-cpu=x86-64'
export FORMAL_CASES_DIR="$PWD/formal/.cache/local-cases"
export FORMAL_SEED=31e62d70b58a940f
cargo +1.97.1 test -p lean-sphincs --release --locked --test formal_conformance -- --ignored --nocapture
cargo +1.97.1 test -p lean-sphincs --release --locked --lib wots::formal::export_lean_components -- --ignored --exact --nocapture
python3 -m unittest discover -s scripts -p test_run_formal.py
python3 scripts/run_formal.py formal/.cache/leanVM/formal/lean_sphincs/.lake/build/bin/signature-kat \
  "$FORMAL_CASES_DIR" --component-binary formal/.cache/leanVM/formal/lean_sphincs/.lake/build/bin/implementation-kat \
  --log formal/.cache/local-comparison.log
python3 scripts/check_formal_rejection.py formal/.cache/leanVM/formal/lean_sphincs/.lake/build/bin/signature-kat \
  "$FORMAL_CASES_DIR" --component-binary formal/.cache/leanVM/formal/lean_sphincs/.lake/build/bin/implementation-kat \
  --log-directory formal/.cache/local-rejection
```

Also reproduce the workflow's independent upstream axiom check for a complete gate. The initial corpus directory must be empty. Use `-C target-cpu=x86-64-v3` on AVX2 hardware and/or `--features asm-keccak` on **both** Cargo commands for the other configurations; select a fresh output directory. Replay downloaded corpora with both binaries from the same proof artifact.

## Aggregate verifier

`lean-verifier` uses a separate immutable VM reference, recorded in
[`reference.json`](../crates/lean-verifier/reference.json), with Lean 4.35.0.
It does not use the signature proof package's newer pin. The existing formal
workflow adds two gates:

* Kernel-check `LeanVM.knowledgeSoundness_holds`, `LeanVM.completeness_holds`,
  `LeanVM.Wire.roundTrip` and `LeanVM.Wire.oneEncoding`, plus the executable
  verifier and wire models. `VerifierAxioms.lean` requires those four theorems
  and rejects transitive dependencies beyond the three foundational axioms.
  Source digests, profile revision, toolchains and forbidden proof escapes are
  checked before building. No kernel-skipping development options are used.
* Generate the pinned native prover's small-program corpus across rates 1–4.
  Compare both honest transports and 256 deterministic verification cases per
  fixture, then run the upstream wire driver's mutations on every phase,
  including the committed golden vector, duplicate/reordered queries, boundary
  sizes, altered leaves/siblings, truncations and trailing bytes. Both default
  and assembly hashing builds compile the actual port's VM source into a
  development-only bridge. Panics, crashes, timeouts, missing results and any
  verdict/byte mismatch fail the gate; two failing processes cannot count as
  agreement.

The generic small-program bridge is not a public verifier API. The library's
fixed aggregation-program identity, full aggregate statement, recursion, pruning,
signature claims and DA binding are exercised by its Rust reference conformance
tests. The Lean proofs concern the pinned mathematical protocol; the differential
checks are finite evidence about this Rust port, including its computed-root
optimization. This is not a universal proof of the Rust implementation.

Run the hosted verifier jobs without rebuilding the signature proof package:

```sh
gh workflow run formal.yml --repo Soubhik-10/lean-crypto --ref YOUR_BRANCH -f verifier_only=true
```

To replay with a checkout at the exact verifier pin and the two checked Linux
model executables downloaded from the matching workflow run:

```sh
reference=/path/to/pinned/leanVM
models=/path/to/lean-verifier-models
fixtures="$PWD/formal/.cache/verifier-fixtures"
python3 -I scripts/check_verifier_reference.py "$reference"
bash "$reference/formal/lean_vm/scripts/export-verifier-fixtures-rust.sh" "$fixtures"
RUSTFLAGS="-C target-cpu=x86-64-v3" cargo build -p lean-verifier --release --locked --example conformance
chmod +x "$models/leanvm-verify" "$models/wire-diff"
python3 -I scripts/check_verifier_conformance.py "$reference" "$fixtures" target/release/examples/conformance \
  --models "$models" --output formal/.cache/verifier-results --jobs 2
```

The replay driver requires Linux/POSIX process resource limits. Use an AVX2-capable
host for the flags above. Add `--features asm-keccak` when building the bridge to
repeat with assembly streaming hashes. Lean builds run on GitHub; replaying the
saved executables does not require installing Lean locally. Proof logs, axiom
reports, the generated corpus, conformance verdicts and failing-case bytes are
retained as CI artifacts. Reuse that saved corpus to replay the exact inputs
instead of regenerating it.

## Remaining trusted dependencies and limits

The Lean kernel, foundational axioms and upstream definitions are trusted for proof checking. Execution/conformance additionally trusts Lean's compiler/runtime, both comparison drivers and parsers, Rust/rustc/LLVM, Alloy/RustCrypto or assembly Keccak, `wide`'s SIMD semantics, CPU behavior and CI infrastructure. The older mathematical schedule theorem alone does not verify the SIMD permutation; the source contracts below prove its per-lane functional behavior. No new proof covers concrete Keccak's cryptographic security, constant time, dependency memory safety, compiler correctness or side-channel behavior. The upstream query-accounting assumptions and signature limit remain part of its theorem; the Rust API does not count a key's signing requests.

Update `upstream.json` deliberately, review the statement, equivalences, security-transfer conditions and executable at the new pin, and run all proof/conformance gates. Reconcile a changed encoding explicitly; never bypass the kernel, weaken the axiom gate or relax comparisons to accept a mismatch.

## Production SPHINCS source verification

This gate proves deterministic functional refinement of the production
`lean-sphincs` crate against EthLib, using Charon/Aeneas translations of the actual
Rust bodies. It covers scalar, SSE2, AVX2, SSE2 with assembly hashing, and AVX2
with assembly hashing. Scalar is extracted for `aarch64-unknown-linux-gnu`;
the four x86 configurations use their production compiler feature selections.

**Final combined audit: passed in all five configurations.** Fresh extraction
and translation, complete source contracts, concrete backend instances, signing
roundtrips, and dependency/mutation audits passed against the observable
standard-library model.

| Main contracts | Established behavior |
| --- | --- |
| `KeyGen.key_gen_ethlib_spec` | Every 32-byte secret produces the encoded public seed and canonical top-tree root. |
| `FullSign.sign_with_limit_ethlib_spec`, `sign_ethlib_spec` | Complete public signing for every `u64` attempt limit, including zero, exact signature bytes on success, and the precise first exhausted layer on failure. Default signing uses `2^32` trials. |
| `WholeVerifier.verify_*_ethlib_spec` | Actual public verification equals EthLib `decodePublicKey`, `decodeSignature` and `verifyWith` for every signature byte string, including all invalid lengths and layer-encoding rejections. Concrete scalar/SSE2/AVX2 contracts discharge the backend premises. |
| `CanonicalCorrectness.sign_with_limit_roundtrip_*`, `sign_roundtrip_*` | Actual key generation, signing and verification compose: every successfully generated signature is accepted; counter exhaustion remains an error. Both bounded and default APIs are covered in all five configurations. |
| `Layout.*`, `CanonicalCorrectness.signature_roundtrip` | Exact public-key and 7,740-byte signature layouts, all counters/FORS/chain/path fields, malformed-length behavior, and lossless typed signature serialization. |
| Source SIMD, FORS, WOTS, tree and cache contracts | Actual lane arithmetic, all 24 Keccak rounds, 64/80-byte hashing, gathers/scatters, queues and scalar tails; all FORS openings and hypertree layers; complete signing-tree/cache construction and exact reader/buffer updates. |
| `ErrorFormatting` in `RustCrypto/Fmt*` | Extracted `SignError` Display, Debug, Clone, equality and Error supertraits, including all byte-valued layers, alternate Debug, writer options and retained partial output on failure. |

These are source functional proofs in the deterministic `Id` model. They trust
the Lean kernel and standard foundations, the pinned Charon/Aeneas translation,
and explicit interface models for Rust standard-library operations, Alloy Keccak
and `wide` words. Alloy streaming hashing is modeled as the accumulated byte
stream hashed by EthLib Keccak; `wide` operations are modeled as ordered 64-bit
lanes. The dependency implementations and their machine code are outside this
proof boundary. The [formatting model](Runtime/README.md) makes output observable;
Rust's default `Error::source` body is not extracted and remains a standard-library
boundary.

No claim is made about cryptographic hardness, constant time or side channels,
hash-query trace equivalence, compiler correctness, or CPU correctness. In
particular, these results do not transfer the older reference's security theorem
or query budget to this Rust execution order. Exhaustion is proved as behavior;
signing success for every key/message is not assumed or promised.

### Pins and reproduction

[`ethlib.json`](ethlib.json) pins EthLib to
`ec1f398c9427e374160e68ce158a39e40805fd25` and records the reference source hashes.
[`extractor.json`](extractor.json) pins Aeneas to
`fb44cb400eb6bfe7dce97422ebe8fa748b7e4f9b`, Charon to
`695be3d6292e988eedd8afcb7a709146a0ff4f01` (version `0.1.324`), Rust to
`nightly-2026-09-17`, OCaml to `5.3.0`, and Lean to `4.36.0`.
Use Linux/WSL, Python 3 and a C toolchain. Build the pinned Charon/Aeneas binaries
and install the Rust extraction components and aarch64 target as shown in the
[source workflow](../.github/workflows/sphincs-source.yml). Keep WSL runtime and
Cargo caches on native Linux storage.

From the repository root, with those binaries and Lean on `PATH`:

```sh
set -euo pipefail
runtime=/absolute/path/to/sphincs-runtime
charon=/absolute/path/to/charon
aeneas=/absolute/path/to/aeneas

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

Extraction automatically supplies Charon's `--sysroot default`. All five
configurations are required by the source gate. Extraction or translation alone
is not a proof. `prepare_batching.py` prepares the pinned EthLib closure; the Lake
`Batching` target retains only `Batching.Keccak` and `Batching.Constants`, used by
the source proofs. Runtime preparation preserves the stock Aeneas sources and
builds the documented formatting replacements separately with their importers.

`SourceAudit` requires the main contracts by name and audits their transitive
dependencies, allowing only `propext`, `Classical.choice` and `Quot.sound`.
Generated local Rust bodies must be present and non-opaque. The gate rejects
proof holes and kernel shortcuts, checks source/proof/tool/model identities
before and after checking, and runs rejection controls for changed source,
serialization, SIMD rotation, injected assumptions and missing required
contracts. Successful runs write a fresh `formal/.cache/source-runs/*/evidence.json`;
its trust-boundary and exclusion fields delimit the functional-refinement claim.

[`.github/workflows/sphincs-source.yml`](../.github/workflows/sphincs-source.yml)
rebuilds the pinned tools, extracts/translates the five configurations, checks the
observable runtime and runs the source gate on relevant pull requests, pushes to
`main`, weekly, and manually. It retains extraction, translation, runtime-model
and proof evidence. The older security/conformance workflow remains a separate
scope.
