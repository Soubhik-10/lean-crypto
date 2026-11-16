# Configuration sweep

CPU: AMD Ryzen 9 8940HX with Radeon Graphics (16 cores, 32 threads).

Compiler: Rust 1.97.1; LLVM 22.1.6. Optimization level 3, Thin LTO, one codegen unit.

Median time per operation from 11 samples per configuration (1 pass). Adapter speedup = `(lean-sphincs / batched adapter - 1) × 100%`; negative values mean the adapter is slower.

Verification starts from encoded signatures; signing and key generation include serialization. Small differences need confirmation across repeat runs.

The Keccak column selects lean-sphincs' Alloy backend. Verification also uses paired SSE2 FORS hashing in SSE2 and SSE4.2 builds. leanVM uses its own CPU-selected scalar and SIMD paths. Compiler flags apply to both implementations within each row. See the [measurement method and raw data](SUITE.md#published-measurements).

leanVM: [native Rust leanSPHINCS implementation](https://github.com/leanEthereum/leanVM/tree/4937c851eafb9e93bc7436eebe9e6dc8ae4c227a/crates/lean_sphincs).

The batched column is a local experimental adapter over leanVM's public internals. It uses leanVM's SIMD hash API within one signature operation and is not stock leanVM.

### Verification

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (µs) | leanVM (unmodified, pinned revision) (µs) | leanVM + local SIMD batching adapter (µs) | Adapter speedup |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| SSE2 | asm-keccak | enabled | 90.15 | 142.06 | 128.97 | -30.1% |
| SSE2 | asm-keccak | disabled | 89.38 | 138.74 | 127.87 | -30.1% |
| SSE2 | RustCrypto | enabled | 102.46 | 145.04 | 129.46 | -20.9% |
| SSE2 | RustCrypto | disabled | 100.73 | 139.08 | 127.80 | -21.2% |
| SSE2 | tiny-keccak | enabled | 104.96 | 146.38 | 130.53 | -19.6% |
| native | asm-keccak | enabled | 93.85 | 127.47 | 39.69 | +136.5% |
| native | asm-keccak | disabled | 88.01 | 119.63 | 38.73 | +127.2% |
| native | RustCrypto | enabled | 143.05 | 123.19 | 42.66 | +235.4% |
| native | RustCrypto | disabled | 112.83 | 119.47 | 39.46 | +185.9% |
| native | tiny-keccak | disabled | 185.94 | 126.15 | 43.68 | +325.7% |
| SSE4.2 | asm-keccak | enabled | 90.82 | 241.09 | 228.70 | -60.3% |
| SSE4.2 | asm-keccak | disabled | 89.78 | 237.26 | 226.64 | -60.4% |
| SSE4.2 | RustCrypto | enabled | 149.54 | 237.75 | 227.42 | -34.2% |
| SSE4.2 | RustCrypto | disabled | 149.05 | 237.51 | 227.47 | -34.5% |
| SSE4.2 | tiny-keccak | enabled | 153.83 | 241.98 | 229.65 | -33.0% |
| AVX2 | asm-keccak | enabled | 105.31 | 189.41 | 78.92 | +33.4% |
| AVX2 | asm-keccak | disabled | 100.46 | 122.67 | 50.12 | +100.4% |
| AVX2 | RustCrypto | enabled | 137.88 | 149.80 | 60.19 | +129.1% |
| AVX2 | RustCrypto | disabled | 115.78 | 121.43 | 49.93 | +131.9% |
| AVX2 | tiny-keccak | disabled | 119.60 | 126.70 | 50.72 | +135.8% |
| AVX-512 | asm-keccak | enabled | 89.87 | 119.60 | 39.34 | +128.5% |
| AVX-512 | asm-keccak | disabled | 91.38 | 123.42 | 40.03 | +128.2% |
| AVX-512 | RustCrypto | enabled | 117.98 | 122.27 | 39.30 | +200.2% |
| AVX-512 | RustCrypto | disabled | 115.84 | 120.53 | 39.41 | +193.9% |
| AVX-512 | tiny-keccak | disabled | 119.57 | 122.52 | 39.20 | +205.0% |

### Signing

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (unmodified, pinned revision) (ms) | leanVM + local SIMD batching adapter (ms) | Adapter speedup |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| SSE2 | asm-keccak | enabled | 113.88 | 148.12 | 136.21 | -16.4% |
| SSE2 | asm-keccak | disabled | 105.31 | 139.11 | 125.01 | -15.8% |
| SSE2 | RustCrypto | enabled | 140.91 | 153.09 | 129.07 | +9.2% |
| SSE2 | RustCrypto | disabled | 131.57 | 139.17 | 124.91 | +5.3% |
| SSE2 | tiny-keccak | enabled | 147.14 | 152.69 | 135.61 | +8.5% |
| native | asm-keccak | enabled | 94.59 | 123.40 | 24.86 | +280.5% |
| native | asm-keccak | disabled | 88.78 | 118.15 | 22.71 | +291.0% |
| native | RustCrypto | enabled | 159.43 | 125.78 | 26.10 | +510.8% |
| native | RustCrypto | disabled | 111.62 | 119.41 | 22.64 | +393.0% |
| native | tiny-keccak | disabled | 162.34 | 126.67 | 26.02 | +524.0% |
| SSE4.2 | asm-keccak | enabled | 112.19 | 248.88 | 236.93 | -52.6% |
| SSE4.2 | asm-keccak | disabled | 104.57 | 234.43 | 223.32 | -53.2% |
| SSE4.2 | RustCrypto | enabled | 239.88 | 242.47 | 236.64 | +1.4% |
| SSE4.2 | RustCrypto | disabled | 227.78 | 234.69 | 224.19 | +1.6% |
| SSE4.2 | tiny-keccak | enabled | 241.93 | 250.84 | 239.96 | +0.8% |
| AVX2 | asm-keccak | enabled | 103.82 | 198.37 | 56.76 | +82.9% |
| AVX2 | asm-keccak | disabled | 99.47 | 120.61 | 38.63 | +157.5% |
| AVX2 | RustCrypto | enabled | 142.26 | 151.25 | 46.71 | +204.6% |
| AVX2 | RustCrypto | disabled | 115.76 | 119.58 | 38.70 | +199.1% |
| AVX2 | tiny-keccak | disabled | 126.78 | 128.46 | 39.47 | +221.2% |
| AVX-512 | asm-keccak | enabled | 91.68 | 122.82 | 23.03 | +298.1% |
| AVX-512 | asm-keccak | disabled | 94.99 | 124.53 | 24.19 | +292.6% |
| AVX-512 | RustCrypto | enabled | 120.62 | 119.12 | 22.79 | +429.2% |
| AVX-512 | RustCrypto | disabled | 121.70 | 125.24 | 23.98 | +407.5% |
| AVX-512 | tiny-keccak | disabled | 125.82 | 120.47 | 23.67 | +431.5% |

### Key generation

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (unmodified, pinned revision) (ms) | leanVM + local SIMD batching adapter (ms) | Adapter speedup |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| SSE2 | asm-keccak | enabled | 55.28 | 74.41 | 65.65 | -15.8% |
| SSE2 | asm-keccak | disabled | 54.51 | 73.45 | 64.99 | -16.1% |
| SSE2 | RustCrypto | enabled | 73.81 | 74.93 | 65.57 | +12.6% |
| SSE2 | RustCrypto | disabled | 69.05 | 73.37 | 64.99 | +6.2% |
| SSE2 | tiny-keccak | enabled | 73.66 | 75.88 | 67.64 | +8.9% |
| native | asm-keccak | enabled | 50.18 | 65.57 | 12.61 | +297.9% |
| native | asm-keccak | disabled | 46.60 | 61.41 | 11.98 | +289.0% |
| native | RustCrypto | enabled | 72.08 | 65.95 | 13.67 | +427.4% |
| native | RustCrypto | disabled | 58.88 | 61.91 | 12.17 | +383.7% |
| native | tiny-keccak | disabled | 100.89 | 65.75 | 13.59 | +642.2% |
| SSE4.2 | asm-keccak | enabled | 55.78 | 126.39 | 118.51 | -52.9% |
| SSE4.2 | asm-keccak | disabled | 55.01 | 123.19 | 117.11 | -53.0% |
| SSE4.2 | RustCrypto | enabled | 123.64 | 126.44 | 118.85 | +4.0% |
| SSE4.2 | RustCrypto | disabled | 119.79 | 123.75 | 117.25 | +2.2% |
| SSE4.2 | tiny-keccak | enabled | 124.77 | 129.00 | 119.76 | +4.2% |
| AVX2 | asm-keccak | enabled | 54.54 | 105.71 | 30.39 | +79.5% |
| AVX2 | asm-keccak | disabled | 52.42 | 65.90 | 20.38 | +157.2% |
| AVX2 | RustCrypto | enabled | 72.84 | 70.75 | 24.35 | +199.1% |
| AVX2 | RustCrypto | disabled | 60.68 | 62.66 | 20.28 | +199.2% |
| AVX2 | tiny-keccak | disabled | 67.03 | 66.95 | 20.69 | +224.0% |
| AVX-512 | asm-keccak | enabled | 47.22 | 64.95 | 12.27 | +284.9% |
| AVX-512 | asm-keccak | disabled | 48.14 | 63.83 | 12.29 | +291.6% |
| AVX-512 | RustCrypto | enabled | 62.03 | 63.64 | 12.20 | +408.6% |
| AVX-512 | RustCrypto | disabled | 61.28 | 62.45 | 12.16 | +404.1% |
| AVX-512 | tiny-keccak | disabled | 64.23 | 62.95 | 12.21 | +426.0% |

All 25 configurations; 11 samples per operation, one pass. This tuning data is separate from the confirmation results.

[Raw batch times](simd-sweep.json). [Measured source snapshot](https://github.com/Soubhik-10/lean-sphincs/tree/75268418b47f99042c9176a0e8efaa080138a454).
