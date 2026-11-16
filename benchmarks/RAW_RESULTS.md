# Direct public API benchmark

CPU: AMD Ryzen 9 8940HX with Radeon Graphics.

Compiler: rustc 1.97.1 (8bab26f4f 2026-07-14); LLVM version: 22.1.6.

Unmodified library APIs, with each library's native inputs and return values. leanVM verification receives a pre-parsed signature; lean-sphincs verification receives encoded bytes. Input preparation is outside timing. No output serialization is added to signing or key generation.

44 samples per pass, 3 passes. All samples retained.

## Verification

| CPU target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (µs) | leanVM, unmodified (µs) | lean-sphincs speedup |
| --- | --- | --- | ---: | ---: | ---: |
| native | asm-keccak | enabled | 36.87 | 119.79 | +224.9% |
| native | asm-keccak | disabled | 36.68 | 119.05 | +224.5% |
| native | RustCrypto | disabled | 41.84 | 121.57 | +190.6% |
| AVX-512 | asm-keccak | enabled | 36.64 | 122.25 | +233.6% |

## Signing

| CPU target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM, unmodified (ms) | lean-sphincs speedup |
| --- | --- | --- | ---: | ---: | ---: |
| native | asm-keccak | enabled | 89.32 | 119.40 | +33.7% |
| native | asm-keccak | disabled | 90.01 | 120.40 | +33.8% |
| native | RustCrypto | disabled | 118.13 | 120.22 | +1.8% |
| AVX-512 | asm-keccak | enabled | 92.87 | 122.31 | +31.7% |

## Key generation

| CPU target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM, unmodified (ms) | lean-sphincs speedup |
| --- | --- | --- | ---: | ---: | ---: |
| native | asm-keccak | enabled | 46.51 | 62.03 | +33.4% |
| native | asm-keccak | disabled | 46.76 | 62.78 | +34.3% |
| native | RustCrypto | disabled | 60.46 | 62.44 | +3.3% |
| AVX-512 | asm-keccak | enabled | 47.58 | 63.44 | +33.3% |

The lean-sphincs Keccak column selects Alloy hashing; leanVM uses its own hashing code. Both libraries share compiler flags within each row.

## Ecrecover

| Compiler target | Address Keccak | LLVM SLP | Recovery implementation | Time (µs) |
| --- | --- | --- | --- | ---: |
| native | asm-keccak | enabled | libsecp256k1 | 38.86 |
| native | asm-keccak | disabled | libsecp256k1 | 38.67 |
| native | RustCrypto | disabled | libsecp256k1 | 38.90 |
| SSE4.2 | tiny-keccak | enabled | k256 | 50.84 |
| AVX2 | asm-keccak | enabled | k256 | 52.72 |
| AVX-512 | asm-keccak | enabled | libsecp256k1 | 39.16 |

## Fastest confirmed builds

| Operation | Library/provider | Compiler flags | Alloy Keccak in the build |
| --- | --- | --- | --- |
| verify | lean-sphincs | `-C target-cpu=x86-64-v4` | asm-keccak |
| verify | leanVM | `-C target-cpu=native -C no-vectorize-slp` | asm-keccak |
| sign | lean-sphincs | `-C target-cpu=native` | asm-keccak |
| sign | leanVM | `-C target-cpu=native` | asm-keccak |
| key_gen | lean-sphincs | `-C target-cpu=native` | asm-keccak |
| key_gen | leanVM | `-C target-cpu=native` | asm-keccak |
| libsecp256k1 | evm2 | `-C target-cpu=native -C no-vectorize-slp` | asm-keccak |
| k256 | evm2 | `-C target-cpu=x86-64-v2` | tiny-keccak |

The Alloy column identifies the shared build configuration; it does not change leanVM’s hashing backend. Headline percentages use the lowest complete median for each implementation and operation, not individual samples or passes.

Candidates were selected from [17 fresh screening builds](raw-api-screening.json), followed by five builds in separate three-pass confirmation. The later full matrix selected 1 additional recovery builds for the same confirmation scope. Screening and full-matrix samples are excluded from confirmation medians.

Measured source: [`ffd83f9`](https://github.com/Soubhik-10/lean-sphincs/tree/ffd83f95d9d5fa28e27115c976a12a1f765e157b). [Raw confirmation measurements](raw-api-measurements.json). [Exact API calls and method](SUITE.md#direct-public-api-comparison).

## Full matrix results

These separate measurements cover all 30 CPU/hash/recovery configurations with
44 samples per case. They are not mixed into the three-pass confirmation above.

### Verification

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (µs) | leanVM (µs) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 102.43 | 143.97 | +40.5% |
| SSE2 | tiny-keccak | enabled | 106.97 | 143.23 | +33.9% |
| SSE2 | asm-keccak | enabled | 91.09 | 143.22 | +57.2% |
| SSE4.2 | RustCrypto | enabled | 151.26 | 242.61 | +60.4% |
| SSE4.2 | tiny-keccak | enabled | 154.65 | 242.92 | +57.1% |
| SSE4.2 | asm-keccak | enabled | 91.33 | 242.83 | +165.9% |
| AVX2 | RustCrypto | enabled | 91.42 | 121.46 | +32.9% |
| AVX2 | tiny-keccak | disabled | 71.23 | 122.79 | +72.4% |
| AVX2 | asm-keccak | enabled | 50.49 | 121.65 | +140.9% |
| AVX-512 | RustCrypto | enabled | 41.61 | 121.12 | +191.1% |
| AVX-512 | tiny-keccak | disabled | 41.84 | 123.31 | +194.7% |
| AVX-512 | asm-keccak | enabled | 36.51 | 122.10 | +234.4% |
| native | RustCrypto | enabled | 41.73 | 121.75 | +191.7% |
| native | tiny-keccak | disabled | 41.46 | 122.14 | +194.6% |
| native | asm-keccak | enabled | 36.73 | 118.99 | +224.0% |

### Signing

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 135.73 | 143.94 | +6.0% |
| SSE2 | tiny-keccak | enabled | 137.84 | 144.09 | +4.5% |
| SSE2 | asm-keccak | enabled | 108.02 | 143.92 | +33.2% |
| SSE4.2 | RustCrypto | enabled | 235.22 | 246.57 | +4.8% |
| SSE4.2 | tiny-keccak | enabled | 236.09 | 244.14 | +3.4% |
| SSE4.2 | asm-keccak | enabled | 106.63 | 242.49 | +127.4% |
| AVX2 | RustCrypto | enabled | 119.95 | 123.58 | +3.0% |
| AVX2 | tiny-keccak | disabled | 121.25 | 121.96 | +0.6% |
| AVX2 | asm-keccak | enabled | 102.17 | 121.22 | +18.7% |
| AVX-512 | RustCrypto | enabled | 117.60 | 121.30 | +3.2% |
| AVX-512 | tiny-keccak | disabled | 121.35 | 122.40 | +0.9% |
| AVX-512 | asm-keccak | enabled | 92.01 | 122.20 | +32.8% |
| native | RustCrypto | enabled | 116.56 | 120.91 | +3.7% |
| native | tiny-keccak | disabled | 112.56 | 123.72 | +9.9% |
| native | asm-keccak | enabled | 88.00 | 117.41 | +33.4% |

### Key generation

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 70.80 | 75.54 | +6.7% |
| SSE2 | tiny-keccak | enabled | 73.38 | 75.63 | +3.1% |
| SSE2 | asm-keccak | enabled | 55.30 | 75.94 | +37.3% |
| SSE4.2 | RustCrypto | enabled | 122.99 | 127.29 | +3.5% |
| SSE4.2 | tiny-keccak | enabled | 123.98 | 127.38 | +2.7% |
| SSE4.2 | asm-keccak | enabled | 55.58 | 127.02 | +128.5% |
| AVX2 | RustCrypto | enabled | 62.09 | 64.23 | +3.5% |
| AVX2 | tiny-keccak | disabled | 64.52 | 63.37 | -1.8% |
| AVX2 | asm-keccak | enabled | 53.05 | 64.74 | +22.0% |
| AVX-512 | RustCrypto | enabled | 61.21 | 64.03 | +4.6% |
| AVX-512 | tiny-keccak | disabled | 63.36 | 63.95 | +0.9% |
| AVX-512 | asm-keccak | enabled | 48.07 | 64.94 | +35.1% |
| native | RustCrypto | enabled | 60.43 | 63.22 | +4.6% |
| native | tiny-keccak | disabled | 60.72 | 63.51 | +4.6% |
| native | asm-keccak | enabled | 46.48 | 62.47 | +34.4% |

### All recovery builds

| Compiler target | Address Keccak | LLVM SLP | libsecp256k1 (µs) | k256 (µs) | libsecp256k1 faster |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 39.24 | 51.68 | +31.7% |
| SSE2 | tiny-keccak | enabled | 39.21 | 51.83 | +32.2% |
| SSE2 | asm-keccak | enabled | 39.06 | 51.41 | +31.6% |
| SSE4.2 | RustCrypto | enabled | 39.26 | 50.74 | +29.3% |
| SSE4.2 | tiny-keccak | enabled | 39.25 | 50.61 | +28.9% |
| SSE4.2 | asm-keccak | enabled | 39.02 | 50.85 | +30.3% |
| AVX2 | RustCrypto | enabled | 39.03 | 50.93 | +30.5% |
| AVX2 | tiny-keccak | disabled | 39.15 | 52.34 | +33.7% |
| AVX2 | asm-keccak | enabled | 39.03 | 50.77 | +30.1% |
| AVX-512 | RustCrypto | enabled | 38.66 | 50.95 | +31.8% |
| AVX-512 | tiny-keccak | disabled | 39.01 | 52.04 | +33.4% |
| AVX-512 | asm-keccak | enabled | 38.88 | 51.12 | +31.5% |
| native | RustCrypto | enabled | 39.09 | 50.81 | +30.0% |
| native | tiny-keccak | disabled | 39.07 | 52.07 | +33.3% |
| native | asm-keccak | enabled | 38.51 | 51.49 | +33.7% |

[Full raw matrix](raw-api-matrix.json).
