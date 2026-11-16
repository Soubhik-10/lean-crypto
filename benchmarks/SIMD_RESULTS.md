# SIMD confirmation results

Historical experiment: the local SIMD column is a separate implementation using
leanVM primitives, not unmodified upstream leanVM. The current stock-library
comparison is in [RAW_RESULTS.md](RAW_RESULTS.md).

CPU: AMD Ryzen 9 8940HX with Radeon Graphics (16 cores, 32 threads).

Compiler: Rust 1.97.1; LLVM 22.1.6. Optimization level 3, Thin LTO, one codegen unit.

Median time per operation from 132 samples per configuration (3 passes). Adapter speedup = `(lean-sphincs / batched adapter - 1) × 100%`; negative values mean the adapter is slower.

Verification starts from encoded signatures; signing and key generation include serialization. Small differences need confirmation across repeat runs.

The Keccak column selects lean-sphincs' Alloy backend. Verification also uses paired SSE2 FORS hashing in SSE2 and SSE4.2 builds. leanVM uses its own CPU-selected scalar and SIMD paths. Compiler flags apply to both implementations within each row. See the [measurement method and raw data](SUITE.md#published-measurements).

leanVM: [native Rust leanSPHINCS implementation](https://github.com/leanEthereum/leanVM/tree/4937c851eafb9e93bc7436eebe9e6dc8ae4c227a/crates/lean_sphincs).

The batched column is a local experimental adapter over leanVM's public internals. It uses leanVM's SIMD hash API within one signature operation and is not stock leanVM.

### Verification

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (µs) | leanVM (unmodified, pinned revision) (µs) | leanVM + local SIMD batching adapter (µs) | Adapter speedup |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| native | asm-keccak | disabled | 88.33 | 119.94 | 38.71 | +128.2% |
| native | RustCrypto | disabled | 112.18 | 119.12 | 38.97 | +187.8% |

### Signing

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (unmodified, pinned revision) (ms) | leanVM + local SIMD batching adapter (ms) | Adapter speedup |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| native | asm-keccak | disabled | 89.02 | 119.58 | 22.72 | +291.7% |
| native | RustCrypto | disabled | 112.31 | 119.05 | 22.76 | +393.4% |

### Key generation

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (unmodified, pinned revision) (ms) | leanVM + local SIMD batching adapter (ms) | Adapter speedup |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| native | asm-keccak | disabled | 46.69 | 61.68 | 12.08 | +286.5% |
| native | RustCrypto | disabled | 58.70 | 62.31 | 12.14 | +383.6% |

Two preselected builds; 44 samples per pass, three passes.

[Raw batch times](simd-confirmation.json). [Measured source snapshot](https://github.com/Soubhik-10/lean-sphincs/tree/75268418b47f99042c9176a0e8efaa080138a454).
