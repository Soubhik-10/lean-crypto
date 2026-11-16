# Coverage-guided differential fuzzing

The libFuzzer targets call the implementation and the pinned comparison library
through the same oracles as the large randomized test runner. They fail on
panics, differing verification outcomes, key differences or signature differences.
Cargo-fuzz instruments Rust coverage and uses AddressSanitizer by default.

| Target | Input and checks |
| --- | --- |
| `verify_wire` | Public key, message and arbitrary-length signature bytes; compare both verifiers. |
| `mutate_valid` | Edits to a valid fixture, including counters and later tree paths; compare both verifiers. Unedited inputs exercise successful verification. |
| `sign_differential` | Secret seed and message; compare key generation, deterministic signing, cross-verification and field mutations. This target is deliberately slower. |

The corpus seeder reads the repository's pinned CC0 EthLib data. It provides
valid signatures, malformed lengths, edits throughout every layer and two signing
seeds. For long campaigns, `--full-signing-corpus` adds known answers and
boundary patterns. The small default lets signing fuzzers reach mutations quickly. Corpus initialization preserves discoveries
from previous runs. Generated corpora and crash artifacts stay out of Git.

On Linux or another supported sanitizer environment:

    cargo +nightly-2026-10-20 install cargo-fuzz --version 0.13.2 --locked
    python3 scripts/seed_fuzz.py
    cargo +nightly-2026-10-20 fuzz run verify_wire fuzz/corpus/verify_wire -- -max_total_time=600 -max_len=7805 -timeout=120 -print_final_stats=1
    cargo +nightly-2026-10-20 fuzz run mutate_valid fuzz/corpus/mutate_valid -- -max_total_time=600 -max_len=257 -timeout=120 -print_final_stats=1
    cargo +nightly-2026-10-20 fuzz run sign_differential fuzz/corpus/sign_differential -- -max_total_time=600 -max_len=64 -timeout=120 -print_final_stats=1

Pass `--features asm-keccak` or `--features tiny-keccak` before `--` to test
another backend. Use the same compiler flags when reproducing a failure.
To exercise the paired SSE2 path set `RUSTFLAGS="-C target-cpu=x86-64"`.
CPU-tuned builds exercise the compiler-selected path; the tiny-keccak workaround
adds `-C no-vectorize-slp` without disabling explicitly written SIMD.

Replay any crash directly:

    cargo +nightly-2026-10-20 fuzz run verify_wire fuzz/artifacts/verify_wire/crash-HASH

Replace the target with the one that produced the artifact. `cargo fuzz tmin`
can reduce a crashing input before turning it into a permanent regression test.
The wire encoding is 32 public-key bytes, 32 message bytes, then signature bytes.
Mutation inputs start with a fixture selector followed by four-byte edit records.
Signing inputs are zero-padded to 64 bytes; the first half is the secret seed.

The CI workflow retains corpus caches, crash artifacts and execution statistics.
It configures short PR runs and longer nightly campaigns for baseline RustCrypto,
CPU-tuned assembly and CPU-tuned tiny-keccak builds. Local corpus counts alone
are not execution counts; inspect libFuzzer's coverage and final statistics.
