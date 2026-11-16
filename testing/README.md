# Randomized differential testing

This isolated test package compares this crate with the Rust leanSPHINCS
implementation in leanVM at `f7ba4999ae523b94c8d0969b32762c3effea4cbd`.
The Git revision and lockfile are fixed; no neighboring checkout is required.
The production library gains no reference, RNG or JSON dependency.

Every generated case checks public-key equality, all 7,740 signature bytes,
and verification of both implementations' signatures by both verifiers.
One case in 64 repeats both signers to check determinism. Each case also checks
mutations of the randomizer, FORS secret and path, every layer's counter, chain
values and authentication path, public key, message, key-half order, truncations
and trailing bytes. Both verifiers must agree and reject these single mutations.

Run 10,000 independent random seed/message pairs:

    cargo +1.97.1 run --release --locked --manifest-path testing/Cargo.toml --bin differential -- --cases 10000 --jobs 8

Use `--features asm-keccak` or `--features tiny-keccak` before `--bin` to select
another hashing implementation. `RUSTFLAGS` selects CPU compilation flags.
For the affected CPU-tuned tiny-keccak configuration, include
`-C no-vectorize-slp` through the final Thin LTO build.

An omitted master seed comes from the operating system and is printed and saved.
Each case uses a separate ChaCha20 stream identified by its index. Results are
independent of thread scheduling. `--seed` accepts exactly 32 hexadecimal bytes;
`--start` selects a range for sharding or replay. These seeds are test inputs.

Summaries and counterexamples are saved under ignored `testing/results`.
A failure records the master seed, index, actual input, stage, mismatched bytes
and, for a verification mismatch, a `.wire` file accepted by the raw fuzzer.
Replay the recorded index with:

    cargo +1.97.1 run --release --locked --manifest-path testing/Cargo.toml --bin differential -- --seed MASTER_SEED --start CASE_INDEX --cases 1 --jobs 1 --out testing/results/replay

A run passes only when every requested case completes. A panic or mismatch stops
new work and returns a failing exit status. Build metadata records compiler,
flags, reference revision and a digest of source bytes embedded at compilation.
The run also records Git status, elapsed time and actual comparison counts.

The security workflow configures 256 cases per push/PR and 10,000 per nightly
job, covering the three hash backends, baseline/CPU-tuned x86-64, and ARM64.
Manual workflow dispatch accepts a larger campaign size. Tests supplement
independent security review; passing them does not establish an audit.
