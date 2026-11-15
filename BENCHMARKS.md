# Benchmark measurements

Measured 15 November 2026.

- CPU: AMD Ryzen 9 8940HX (16 cores / 32 threads).
- Host: windows / x86_64, MSVC target.
- Affinity: Windows processor affinity 0x100 (logical CPU 8).
- Compiler: `rustc 1.97.1 (8bab26f4f 2026-07-14)`.
- Release benchmark profile: thin LTO, one codegen unit; no `target-cpu=native` override.
- 30 samples per operation, calibrated batches of at least 100 ms.
- Timed ecrecover implementation: evm2's actual `Crypto` provider, libsecp256k1 backend.

Both evm2 and Alloy are fetched from immutable official Git revisions. The
benchmark does not read or build any neighboring checkout.

- evm2: `git+https://github.com/alloy-rs/evm2?rev=e681662b6d9ec59edafd112f7c8d64f49f1e6dd1#e681662b6d9ec59edafd112f7c8d64f49f1e6dd1`.
- Alloy: `git+https://github.com/alloy-rs/core?rev=70a63bd609da78dcf03e593ae772fec883ce7768#70a63bd609da78dcf03e593ae772fec883ce7768`.

## Time per operation

| Keccak backend | Operation | Median (us) | p05 (us) | p95 (us) |
| --- | --- | ---: | ---: | ---: |
| Default / RustCrypto | evm2/ecrecover | 83.82 | 83.72 | 83.98 |
| Default / RustCrypto | lean_sphincs/valid | 289.90 | 289.44 | 291.97 |
| Default / RustCrypto | lean_sphincs/late_reject | 289.47 | 289.19 | 290.24 |
| Alloy assembly | evm2/ecrecover | 84.18 | 83.60 | 117.90 |
| Alloy assembly | lean_sphincs/valid | 226.26 | 225.78 | 226.77 |
| Alloy assembly | lean_sphincs/late_reject | 226.11 | 225.85 | 226.98 |

The percentiles describe batch-average ns/op, not individual-call latency.
The assembly ecrecover run had some slower samples; its median remained close
to the default-backend median. Raw, chronological samples are retained in
[portable.json](benchmarks/portable.json) and [asm-keccak.json](benchmarks/asm-keccak.json).

Valid verification rotates all three positive EthLib cases. Late rejection
changes the last authentication-path byte, so all chain encodings remain valid
and the verifier does the full work before rejecting. Parsing fixture JSON,
signing the ecrecover fixture, provider initialization and calibration are outside
the timed samples. Compact-signature parsing, key recovery, serialization and
address hashing are included in evm2's measured provider call.

## CPU-time gas ratios

| Keccak backend | Verify / ecrecover | Ratio x 3,000 gas | Ratio x 2,800 frame gas |
| --- | ---: | ---: | ---: |
| Default / RustCrypto | 3.459x | 10376 | 9684 |
| Alloy assembly | 2.688x | 8064 | 7526 |

Assembly Keccak reduced median verification time by 22.0% in these runs.

These are local CPU-time estimates, not proposed consensus gas prices. The
Windows/MSVC libsecp256k1 baseline is platform dependent; it cannot be directly
substituted for measurements on other platforms or implementations. Cross-client and
cross-hardware measurements are needed to judge a price such as 12,600 gas.
The arithmetic excludes calldata/data-floor gas, bandwidth, aggregation and
transaction execution. It does not establish that 12,600 is high or low.

## Validation

- All 26 pinned EthLib verification cases pass.
- Every signature/public-key/message byte is tested with a one-bit mutation.
- Every truncation, appended bytes and 512 deterministic arbitrary full-length encodings are checked.
- Allocation counting reports zero allocations during valid verification.
- Release tests pass with default and assembly Keccak.
- Clippy passes with warnings denied for the library/tests and all-feature benchmark harness.
- Rust 1.90 library check with no default features and documentation generation pass.

## Source fingerprints

These measurements were collected from
[`f647032`](https://github.com/Soubhik-10/lean-sphincs/commit/f647032dcf9397389962e1e3070aafee8b534713),
before the verifier was split into modules. The fingerprints identify that measured
revision:

- `src/lib.rs`: `1ab0d77b319dcee12d8e15e05e7ef2fa8bc1012f225fea1245680aa0011ad00a`.
- `src/verifier.rs`: `a16716885d5f4e89df076df68c55a3fa8b3e9c39825fd677e7abb0be81972095`.

Reproduction commands and methodology are in [the harness README](benchmarks/evm2/README.md).
