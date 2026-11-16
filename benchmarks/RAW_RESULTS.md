# Direct public API benchmark

CPU: AMD Ryzen 9 8940HX with Radeon Graphics.

Compiler: rustc 1.97.1 (8bab26f4f 2026-07-14); LLVM version: 22.1.6.

Unmodified library APIs, with each library's native inputs and return values. leanVM verification receives a pre-parsed signature; lean-sphincs verification receives encoded bytes. Input preparation is outside timing. No output serialization is added to signing or key generation.

44 samples per pass, 3 passes. All samples retained.

## Verification

| CPU target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (µs) | leanVM, unmodified (µs) | lean-sphincs speedup |
| --- | --- | --- | ---: | ---: | ---: |
| native | asm-keccak | disabled | 89.09 | 119.29 | +33.9% |
| native | RustCrypto | disabled | 113.22 | 121.39 | +7.2% |
| AVX-512 | RustCrypto | enabled | 120.33 | 121.51 | +1.0% |

## Signing

| CPU target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM, unmodified (ms) | lean-sphincs speedup |
| --- | --- | --- | ---: | ---: | ---: |
| native | asm-keccak | disabled | 90.52 | 121.47 | +34.2% |
| native | RustCrypto | disabled | 118.46 | 121.64 | +2.7% |
| AVX-512 | RustCrypto | enabled | 123.08 | 121.02 | -1.7% |

## Key generation

| CPU target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM, unmodified (ms) | lean-sphincs speedup |
| --- | --- | --- | ---: | ---: | ---: |
| native | asm-keccak | disabled | 47.01 | 63.47 | +35.0% |
| native | RustCrypto | disabled | 59.71 | 62.42 | +4.5% |
| AVX-512 | RustCrypto | enabled | 63.22 | 63.33 | +0.2% |

[Raw measurements](raw-api-measurements.json). [Method](SUITE.md#direct-public-api-comparison).
