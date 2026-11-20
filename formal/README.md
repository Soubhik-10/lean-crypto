# Lean proofs and implementation conformance

The source of the Lean specification and proofs is leanEthereum/leanVM at the immutable revision in [upstream.json](upstream.json). That repository documents its formalization as vendored from [Verified-zkEVM/leanerVM](https://github.com/Verified-zkEVM/leanerVM). We consume its existing SPHINCS proof and executable model without modifying their definitions or adding axioms. The external source and its license files are fetched into an ignored cache; generated corpora and proof outputs are artifacts, not committed data.

## What CI checks

1. Check out the exact upstream revision and verify its Lean toolchain matches the pin. Keep the upstream Lake manifests unchanged; do not run `lake update`.
2. Scan `Statement`, `common` and `lean_sphincs` for proof escapes and forbid kernel-skipping options in their Lake configuration.
3. Run upstream's memory-aware `lake-build.py` on `Sphincs`, `FORS`, `FORS.Axioms` and `signature-kat`, with Lean's kernel enabled. No `--dev` build is used.
4. Independently print the axiom footprints of `Sphincs.leanSphincsStronglyUnforgeable`, `FORS.Lifetimes.h26_layered_adversary` and `FORS.h26_layered`, allowing only Lean's `propext`, `Classical.choice` and `Quot.sound` axioms, as upstream CI does.
5. Run the current Rust implementation on all pinned vectors and generated cases in each SSE2/AVX2 and RustCrypto/assembly configuration. The exporter writes its actual outputs into the YAML format the upstream `signature-kat` executable consumes. Lean recomputes those outputs from the specification. Signatures must match byte for byte, and verification verdicts must agree.
6. Require an `ok` line for every manifest entry and a zero-mismatch summary, so an empty or partly skipped corpus cannot pass. Save the axiom report, build log, input corpus, seed and comparison log as workflow artifacts.

The default corpus contains the 35 pinned cases plus two generated seed/message pairs with mutations of signature fields, public keys and messages, truncations, trailing bytes and zeroed signatures. `FORMAL_CASES` accepts 1 through 16 generated pairs. `FORMAL_SEED` is a nonzero hexadecimal 64-bit value; CI derives it from the tested commit so every backend receives identical inputs. The manifest records the seed and build configuration.

The model's parser represents malformed inputs as `none` (`null` in the vectors). This crate's public key and message are fixed-size types, so invalid lengths cannot be passed to those APIs. For malformed signature lengths, the exporter first requires Rust to return `false`, then writes `null` to match the Lean parser's rejection. Exact-size signatures, including invalid ones, are compared using the actual Boolean verdict without normalization.

## What the evidence means

The upstream theorem proves strong unforgeability of the formal scheme in the random-permutation model with its stated bounds and assumptions. The Rust-to-Lean comparisons are finite conformance tests, matching the separation of proof and differential testing used by leanVM. They are not a proof of all executions of this independently implemented Rust library. They do not prove memory safety of dependencies, constant-time execution, side-channel resistance, compiler correctness or the cryptographic assumptions for concrete Keccak. See upstream's [statement of scope](https://github.com/leanEthereum/leanVM/blob/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/formal/statement.tex).

## Local reproduction

Use Linux/WSL, Rust 1.97.1, Python 3, a C toolchain and the Lean toolchain named in `upstream.json`. Use an existing leanVM checkout at the exact pinned revision. Run the proof gate from its `formal/lean_sphincs` directory:

```sh
lake exe cache get
python3 -I ../tools/escape-scan.py ../Statement ../common .
python3 -I ../lake-build.py . Sphincs FORS FORS.Axioms signature-kat
```

Run the external axiom check from the workflow as well when reproducing the complete proof gate. From this repository, export a fresh corpus and compare it with that checkout's compiled model:

```sh
export RUSTFLAGS='-C target-cpu=x86-64'
export FORMAL_CASES_DIR="$PWD/formal/.cache/local-cases"
export FORMAL_SEED=31e62d70b58a940f
cargo +1.97.1 test --release --locked --test formal_conformance -- --ignored --nocapture
python3 -m unittest discover -s scripts -p test_run_formal.py
python3 scripts/run_formal.py /path/to/leanVM/formal/lean_sphincs/.lake/build/bin/signature-kat \
  "$FORMAL_CASES_DIR" --log formal/.cache/local-comparison.log
```

The output directory must be empty to prevent stale cases from affecting a run. For AVX2, use `-C target-cpu=x86-64-v3` on hardware that supports it. For assembly hashing, add `--features asm-keccak` to the Cargo command and choose a new output directory. Replay a downloaded CI corpus by passing its directory and the executable from the same upstream pin to `run_formal.py`.

## Updating the reference

Update `upstream.json` deliberately, inspect upstream changes to `Statement/LeanSphincs.lean`, the SPHINCS proof, the executable parser and its dependencies, and keep the documented revision links in step. Run both the proof and conformance jobs before accepting an update. A changed scheme or encoding must be reconciled explicitly; do not weaken the theorem, bypass the kernel or relax result comparisons to make a mismatch pass.
