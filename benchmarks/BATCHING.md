# Batching within one signature

Our verifier groups independent hashes inside a single `verify()` call. It
still checks one complete public key/message/signature at a time. No other
signature is needed to fill a batch, and the algorithm's parameters are unchanged.

## How it works

The 24 FORS authentication paths are independent until their roots are combined.
On AVX2-capable builds, four paths advance together. WOTS+C recovery buffers a
window of 16 chain values, groups active steps four at a time and hashes any
remainder individually. Results are combined in signature order. Dependencies
within each path/chain, and between hypertree layers, remain sequential.

Each SIMD word contains the same 64-bit lane from four independent Keccak
states. One vector instruction updates those four states together. There are
still 515 logical Keccak permutations per valid signature. The source selects
four lanes under AVX2; the native build on this CPU also uses AVX-512VL
instructions. This is a native-build result, not an AVX2-only measurement.

## Why leanVM differs

The measured upstream revision already provides multi-state SIMD Keccak:
[PR #758](https://github.com/leanEthereum/leanVM/pull/758) discusses its AVX-512,
AVX2 and NEON backends. Its public SPHINCS verifier nevertheless walks
[FORS trees](https://github.com/leanEthereum/leanVM/blob/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b/crates/lean_sphincs/src/fors.rs)
and [WOTS chains](https://github.com/leanEthereum/leanVM/blob/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b/crates/lean_sphincs/src/wots.rs)
sequentially through its single-state hasher. That hasher uses optimized AVX-512
code on this machine; there is no missing Cargo feature to enable batching.

The same recovery helpers also supply ordered inputs to
[aggregation hint generation](https://github.com/leanEthereum/leanVM/blob/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b/crates/aggregation/src/hints.rs).
A batching rewrite must preserve those interfaces and ordering requirements.
The inspected code/history establishes the scheduling difference, but does not
state the maintainers' reason for leaving this verifier sequential. Treat this
as an optimization opportunity, rather than an intentional design decision we
can attribute to them. Upstream could use a similar schedule.

## Measured gain

AMD Ryzen 9 8940HX, Windows x86-64 MSVC, Rust 1.97.1 / LLVM 22.1.6. Both libraries
use opt-level 3, native CPU features, Thin LTO and one codegen unit. Assembly
inspection confirms upstream's ZMM permutation instructions and our SIMD/Alloy
assembly paths.

| Configuration | Verify median (µs) |
| --- | ---: |
| Our normal native library | 36.907 |
| Our FORS batching disabled | 69.769 |
| Our WOTS batching disabled | 54.332 |
| Both batching paths disabled | 87.571 |
| Batching disabled, leanVM single-state hash backend | 109.417 |
| Unmodified leanVM | 119.276 |

Disabling only batching slows our verifier **2.37x**. Replacing its single-state
hash backend with upstream's adds **1.25x** with batching disabled. A remaining
**1.09x** difference is not independently attributed. Together the normal
native verifier is **3.23x** faster than the measured upstream verifier.
The signing tree cache does not run during verification.

Controls use temporary source copies, selecting existing scalar recovery
functions while retaining native flags. An unchanged copy measures 36.900 µs,
close to the original library's 36.907 µs. Upstream parsing is excluded from
timing; our API consumes signature bytes.

## Equivalence checks

Both use 16-byte nodes, 24 FORS trees of height 10, 64 base-4 WOTS+C chains with
target sum 128, hypertree heights 8/8/10, a 32-byte `PK.seed || PK.root` key,
32-byte messages and 7,740-byte signatures. Addresses are 32 bytes; counters
are big-endian 32-bit values.

Separate instrumented builds recorded every hash preimage. Across all eleven
fixtures, both produce the same **491 byte-identical inputs as multisets**, and
515 logical permutations. An upstream permutation-entry counter independently
records 515 calls. Tracing is excluded from timing. Parser roundtrips, selected
signature mutations and the existing native batched-hash tests also pass.
This is conformance evidence for tested inputs, not a security proof.

## Tradeoffs

| Cost | Consequence |
| --- | --- |
| More scheduling code | Address domains, chain steps, lane order and scalar remainders need differential tests. The simple sequential implementation is easier to review. |
| More live state | Multiple sponge states, addresses and buffered nodes increase register/stack pressure. Packing, shuffling and spills can erase gains on another compiler or CPU. |
| Finite batch utilization | Some WOTS steps leave fewer than four active chains; scalar cleanup and packing have a cost. Dependent hashes cannot all be parallelized. |
| Target-specific path | SSE2 gets two-lane FORS; the four-lane FORS/WOTS path requires AVX2. ARM currently uses the selected Alloy backend without this x86 batching path. Native binaries must be deployed to compatible CPUs. |
| Separate proof workload | A faster native verifier does not establish faster proof generation or recursive aggregation. Those paths need their own measurements. |

Verification remains allocation-free. Batching changes execution scheduling,
not the signature size, cryptographic parameters or amount of logical hash work.

## Limits

The main table pools all 132 samples per operation from three fresh processes.
Kernels run in randomized order with 300 ms warmup and adaptive batches targeting
20 ms. The initial batching-only campaign has another three processes; all
2,376 batch samples are retained separately. CPU 8 affinity and AboveNormal
priority are verified before timing. AC power and the Balanced policy are
retained; sibling CPU 9 is not reserved and clocks/temperature are not measured.

The [earlier recovery campaign](README.md#leanvm-and-ecrecover) retains one
process where our control took 52.141 µs, giving about 2.32x against upstream.
The cause remains unresolved. It did not recur in the six relinked audit
processes, whose original-library medians span 36.807–37.039 µs. The 3.23x figure
applies to the tested native build and CPU, not every target or process layout.

Source: this crate at `138d55f3f1b85300c8f7929160882f3508a3fa81`; leanVM at
`6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b`; Alloy at
`70a63bd609da78dcf03e593ae772fec883ce7768`.

[All samples, hash traces, build commands, temporary patches, tests and assembly evidence](data/optimization-audit-2026-11-18.json).
