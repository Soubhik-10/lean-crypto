# Parameter and optimization audit

Measured on 18 November 2026, AMD Ryzen 9 8940HX, Windows x86-64 MSVC,
Rust 1.97.1 / LLVM 22.1.6. The matched native verification result is
**36.907 µs for this crate versus 119.276 µs for leanVM**,
or **3.23x**. The controls below explain most of the difference.

## Parameters and work agree

Both implementations use the same Keccak-256 leanSPHINCS configuration:

| Parameter | Both implementations |
| --- | --- |
| Node size | 16 bytes |
| FORS | 24 trees of height 10 |
| WOTS+C | 64 base-4 chains, chain end 3, target sum 128 |
| Hypertree | Three layers, heights 8/8/10 |
| Public key | 32 bytes, `PK.seed || PK.root` |
| Message | 32 bytes |
| Signature | 7,740 bytes |
| Address / counter | FIPS 205 32-byte address / big-endian 32-bit counter |
| Valid verification | 515 logical Keccak-f[1600] permutations |

The audit asserts the compiled upstream constants against this crate's source
constants, and roundtrips each key/signature through upstream's parser without
changing a byte. More strongly, separate instrumented builds record every
logical hash input during verification: **all 491 preimages match byte for
byte as multisets for all eleven fixtures**. Execution order differs because
of batching. An upstream permutation-entry counter records 515 calls per
signature; summing `floor(input_length / 136) + 1` over either trace also gives
515. The shared histogram per signature is 216 inputs of 64 bytes, 3 of 68,
266 of 80, 2 of 84, 1 of 432 and 3 of 1,072 bytes.

Tracing runs separately and is excluded from all timings. The timed variants
also agree with upstream on valid fixtures and thirteen selected signature-bit
mutations per fixture. This is conformance evidence for the tested inputs,
not a security proof or an independent cryptographic audit.

The existing native library tests also pass with `asm-keccak` and
`target-cpu=native`, including the batched-hash comparison against Alloy.

## Both use optimized native code

The original Cargo artifacts record optimization level 3, no debug assertions,
no overflow checks, native CPU flags, Thin LTO and one codegen unit. The audit
relinks those same original library artifacts. Temporary control libraries
are compiled with the same native/release settings.

Upstream has no optional Cargo hash/verification optimization feature to turn
on. Its native verifier calls its own Keccak code, independent of Alloy's
`asm-keccak` switch. Generated assembly confirms calls from upstream's hasher
to `single_avx512::permute`, containing ZMM `vpternlogq`, `vprolq` and
`vprolvq` instructions. Upstream is not being timed as a debug or scalar-only
build.

This crate's FORS/WOTS verifier groups **four independent hash states**. The
source selects four-lane SIMD under AVX2; the native compiler additionally uses
AVX-512VL instructions such as YMM `vpternlogq`, so these measurements are not
an AVX2-only hardware result. Its remaining hashes use Alloy's assembly
backend, also confirmed in the generated calls.

Upstream's AVX-512 single-state path uses vector registers to accelerate one
permutation. Its public native verifier still walks FORS trees and WOTS chains
sequentially. The hash crate's eight-state `hash_many` API is available but
is not called by this verification path. SIMD within one state and SIMD
across independent states are different uses of the hardware; the presence
of AVX-512 does not make these verification schedules equivalent.

## Controlled ablation

Only temporary source copies are changed. Two additional cfg conditions select
the already existing scalar FORS/WOTS recovery functions while retaining native
CPU flags and the assembly hash backend. A second control swaps only the
single-state hash operations and streaming hasher to upstream's public native
Keccak backend. Parameters and signature logic stay unchanged. The unchanged
copy agrees closely with the original library, providing a control for the
temporary crate/relinking boundary.

| Timed configuration | Verification median (µs) |
| --- | ---: |
| Our original native library | 36.907 |
| Temporary copy, batching enabled | 36.900 |
| Our FORS batching disabled | 69.769 |
| Our WOTS batching disabled | 54.332 |
| Our FORS and WOTS batching disabled | 87.571 |
| Our batching disabled, leanVM single-state hash backend | 109.417 |
| Our batching enabled, leanVM single-state hash backend | 40.517 |
| Unmodified leanVM native verifier | 119.276 |

The sequential comparison isolates approximately:

- **2.37x from FORS/WOTS batching**: 87.57 → 36.91 µs.
- **1.25x from the single-state hash backend** with batching disabled: 109.42 → 87.57 µs.
- **1.09x remains** after matching that backend and disabling batching. This remaining difference was not independently attributed; address/preimage construction, streaming and code layout are among the differences still present.

A same-process 80-byte hash control measures Alloy assembly at
0.164 µs and upstream at 0.209 µs per hash.
This supports the backend explanation but does not equate one short hash with
the entire signature workload. The signing tree cache does not run during
verification and cannot explain this gap. Upstream receives parsed signatures
before timing, while this crate consumes bytes, so the benchmark boundary
gives upstream the cheaper input preparation.

## Sampling and limits

The backend-swap table pools all 132 samples per operation from three fresh
processes, with randomized kernel order, 300 ms warmup per kernel and adaptive
batches targeting 20 ms. The earlier batching-only control has another three
processes and is retained separately. Together there are 2,376 batch samples;
none are removed. CPU 8 affinity and AboveNormal priority are verified before
the start handshake, and AC power is connected. The Balanced power policy is
unchanged. SMT sibling 9 is not reserved; clocks and temperature are not fixed
or measured. Batch timings measure throughput, not individual-call latency.

The earlier [leanVM/ecrecover campaign](ECRECOVER_RESULTS.md#fresh-upstream-leanvm-versus-evm2-confirmation)
contains one process where our control took 52.141 µs instead of about 37 µs.
That process remains in its dataset and gives only about 2.32x against
upstream. The cause is not isolated. It was not reproduced in the six newly
linked audit processes, whose original-library medians range from 36.807 to
37.039 µs. The results establish a native-build speedup on this CPU, not a
universal ratio for portable builds, ARM, or every process layout.

The audited native implementation/harness source is unchanged from
[`138d55f`](https://github.com/Soubhik-10/lean-sphincs/tree/138d55f3f1b85300c8f7929160882f3508a3fa81).
Upstream is pinned to
[`6a828ecf`](https://github.com/leanEthereum/leanVM/tree/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b),
and Alloy to `70a63bd609da78dcf03e593ae772fec883ce7768`.

[Raw samples, build commands/features, Rust harnesses, temporary source patches,
assembly evidence and all hash preimages](optimization-audit-2026-11-18.json). The raw patches document
the experimental controls; no library implementation was changed for this audit.
