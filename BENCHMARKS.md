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

## Paired FORS hashing

Measured 15 November 2026 on an Intel Core i5-1340P running Windows x86-64
with the MSVC target. Both builds used Rust 1.97.1 (8bab26f4f, LLVM 22.1.6),
thin LTO, one codegen unit, and the default target CPU. Runs were pinned to
logical CPU 2 (affinity mask 0x4). Each before/after pair used the pinned
evm2 Crypto provider with libsecp256k1 and 30 samples of at least 100 ms
per operation. The before binaries were built from baseline revision
[356d55e](https://github.com/Soubhik-10/lean-sphincs/commit/356d55e).

Phase timing on the baseline put roughly 94% of elapsed verification time
in FORS and WOTS+C for both valid and late-rejected signatures. FORS alone
accounted for about 52%. A full verification hashes 24 FORS leaves and
240 FORS parent nodes.

On baseline x86-64, the verifier now processes two independent FORS openings
at a time with SSE2 and feeds their roots to the same streaming hasher in
signature order. The paired permutation follows [FIPS 202, section 3.2][fips202]
and uses the original Keccak padding specified by [the pinned EthLib
configuration][ethlib-sphincs]. AVX2 builds and other targets use Alloy for
each FORS hash. Alloy still handles WOTS+C, root compression, the message
digest, and the hypertree with the selected backend on every target. Short
hashes reuse their stack buffer for the encoded address and payload.

| Alloy Keccak | Operation | Before (us) | After (us) | Time reduction | Time / ecrecover, before to after |
| --- | --- | ---: | ---: | ---: | ---: |
| Default | evm2/ecrecover | 45.55 | 45.77 | | |
| Default | Valid verification | 169.47 | 134.28 | 20.8% | 3.721x to 2.934x |
| Default | Late rejection | 168.87 | 137.42 | 18.6% | 3.708x to 3.003x |
| Assembly | evm2/ecrecover | 46.67 | 46.49 | | |
| Assembly | Valid verification | 135.23 | 123.24 | 8.9% | 2.898x to 2.651x |
| Assembly | Late rejection | 133.40 | 124.03 | 7.0% | 2.859x to 2.668x |

The ratios compare CPU time to the ecrecover median from the same run.
Protocol gas pricing is outside the scope of this crate.

[fips202]: https://csrc.nist.gov/pubs/fips/202/final
[ethlib-sphincs]: https://github.com/ethereum/EthLib/tree/03547dd83f298a63e6dcceff0a0b75f6142490aa/EthLib/Cryptography/Sphincs
