# Direct public API results

Historical campaign. For the maintained summary, see [current Rust results](../README.md).

CPU: AMD Ryzen 9 8940HX (16 cores, 32 threads).

Compiler: Rust 1.97.1; LLVM 22.1.6; x86-64 MSVC target. Optimization level 3,
Thin LTO, one codegen unit.

Direct public APIs of this crate and the unmodified native Rust
[`lean_sphincs` package from leanVM at `6a828ecf`](https://github.com/leanEthereum/leanVM/tree/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b/crates/lean_sphincs).
leanVM has no optional signature/hash Cargo features; compiler target flags
select its own Keccak implementation. The Keccak labels below select our
Alloy backend and do not change leanVM's backend. `experimental-simd` is excluded.

Verification receives encoded bytes in lean-sphincs and native public-key/signature
objects prepared before timing in leanVM. Signing and key generation return
native results and recompute from the seed on every call. No local adapter,
added serialization, or proof-generation work is timed in these tables.

Headline values are each implementation's fastest confirmed complete median:
44 samples per pass, three passes and 11 shared key/message pairs. All samples
are retained. Faster = `(leanVM time / lean-sphincs time − 1) × 100%`, calculated
before rounding. Negative values mean slower.

| Operation | lean-sphincs | leanVM (unmodified) | Faster than leanVM |
| --- | ---: | ---: | ---: |
| Verification (µs) | 35.88 | 119.91 | +234.2% |
| Signing (ms) | 87.93 | 119.64 | +36.1% |
| Key generation (ms) | 46.36 | 61.87 | +33.5% |

[Exact revisions, features, APIs and reproduction](BENCHMARK_SETUP.md) ·
[Every confirmation sample](data/raw-api-measurements.json).

## Fastest confirmed builds

| Operation | Library/provider | Compiler target | Alloy Keccak in build | LLVM SLP | Rust flags |
| --- | --- | --- | --- | --- | --- |
| verify | lean-sphincs | AVX-512 | asm-keccak | enabled | `-C target-cpu=x86-64-v4` |
| verify | leanVM | native | asm-keccak | disabled | `-C target-cpu=native -C no-vectorize-slp` |
| sign | lean-sphincs | native | asm-keccak | enabled | `-C target-cpu=native` |
| sign | leanVM | AVX-512 | asm-keccak | enabled | `-C target-cpu=x86-64-v4` |
| key_gen | lean-sphincs | native | asm-keccak | enabled | `-C target-cpu=native` |
| key_gen | leanVM | native | asm-keccak | enabled | `-C target-cpu=native` |
| ecrecover | evm2/libsecp256k1 | native | asm-keccak | enabled | `-C target-cpu=native` |
| ecrecover | evm2/k256 | SSE4.2 | asm-keccak | enabled | `-C target-cpu=x86-64-v2` |

The Alloy column identifies the shared binary configuration; it does not select leanVM's hashing backend.

## Three-pass confirmation details

132 samples per operation and build. Compiler flags apply to both libraries in each row.

### Verification

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (µs) | leanVM (µs) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| AVX-512 | asm-keccak | enabled | 35.88 | 121.62 | +239.0% |
| native | RustCrypto | disabled | 41.28 | 120.91 | +192.9% |
| native | tiny-keccak | disabled | 40.74 | 121.09 | +197.2% |
| native | asm-keccak | enabled | 36.70 | 121.89 | +232.1% |
| native | asm-keccak | disabled | 36.55 | 119.91 | +228.1% |

### Signing

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| AVX-512 | asm-keccak | enabled | 89.91 | 119.64 | +33.1% |
| native | RustCrypto | disabled | 112.27 | 120.59 | +7.4% |
| native | tiny-keccak | disabled | 113.51 | 122.02 | +7.5% |
| native | asm-keccak | enabled | 87.93 | 121.52 | +38.2% |
| native | asm-keccak | disabled | 89.07 | 120.54 | +35.3% |

### Key generation

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| AVX-512 | asm-keccak | enabled | 47.15 | 63.15 | +33.9% |
| native | RustCrypto | disabled | 58.88 | 62.14 | +5.5% |
| native | tiny-keccak | disabled | 58.74 | 62.17 | +5.8% |
| native | asm-keccak | enabled | 46.36 | 61.87 | +33.5% |
| native | asm-keccak | disabled | 46.79 | 62.27 | +33.1% |


## Full build matrix

44 samples per case and configuration, over the same 11 signature inputs.
The Keccak column selects lean-sphincs' Alloy backend; leanVM uses its own
CPU-selected hashing implementation. LLVM SLP is automatic compiler vectorization;
disabling it leaves explicit SIMD enabled.

### Verification

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (µs) | leanVM (µs) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 100.49 | 141.74 | +41.0% |
| SSE2 | tiny-keccak | enabled | 104.03 | 142.30 | +36.8% |
| SSE2 | asm-keccak | enabled | 89.52 | 141.93 | +58.5% |
| SSE4.2 | RustCrypto | enabled | 148.74 | 236.86 | +59.2% |
| SSE4.2 | tiny-keccak | enabled | 151.13 | 237.34 | +57.0% |
| SSE4.2 | asm-keccak | enabled | 89.49 | 239.14 | +167.2% |
| AVX2 | RustCrypto | enabled | 52.81 | 120.49 | +128.2% |
| AVX2 | tiny-keccak | disabled | 72.74 | 119.17 | +63.8% |
| AVX2 | asm-keccak | enabled | 49.85 | 120.25 | +141.2% |
| AVX-512 | RustCrypto | enabled | 40.61 | 119.30 | +193.8% |
| AVX-512 | tiny-keccak | disabled | 40.84 | 120.80 | +195.8% |
| AVX-512 | asm-keccak | enabled | 35.75 | 122.89 | +243.8% |
| native | RustCrypto | enabled | 41.05 | 119.72 | +191.6% |
| native | tiny-keccak | disabled | 41.17 | 123.58 | +200.2% |
| native | asm-keccak | enabled | 36.59 | 118.09 | +222.7% |

### Signing

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 132.47 | 141.30 | +6.7% |
| SSE2 | tiny-keccak | enabled | 134.31 | 141.63 | +5.5% |
| SSE2 | asm-keccak | enabled | 104.99 | 141.27 | +34.6% |
| SSE4.2 | RustCrypto | enabled | 228.62 | 235.02 | +2.8% |
| SSE4.2 | tiny-keccak | enabled | 229.69 | 235.88 | +2.7% |
| SSE4.2 | asm-keccak | enabled | 105.20 | 236.18 | +124.5% |
| AVX2 | RustCrypto | enabled | 118.73 | 118.40 | -0.3% |
| AVX2 | tiny-keccak | disabled | 117.30 | 119.84 | +2.2% |
| AVX2 | asm-keccak | enabled | 99.49 | 119.48 | +20.1% |
| AVX-512 | RustCrypto | enabled | 114.72 | 119.56 | +4.2% |
| AVX-512 | tiny-keccak | disabled | 120.71 | 119.80 | -0.8% |
| AVX-512 | asm-keccak | enabled | 89.39 | 119.89 | +34.1% |
| native | RustCrypto | enabled | 114.37 | 118.58 | +3.7% |
| native | tiny-keccak | disabled | 112.03 | 118.98 | +6.2% |
| native | asm-keccak | enabled | 87.32 | 117.36 | +34.4% |

### Key generation

| Compiler target | lean-sphincs Keccak | LLVM SLP | lean-sphincs (ms) | leanVM (ms) | Faster than leanVM |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 69.65 | 74.21 | +6.6% |
| SSE2 | tiny-keccak | enabled | 70.19 | 74.45 | +6.1% |
| SSE2 | asm-keccak | enabled | 54.75 | 74.13 | +35.4% |
| SSE4.2 | RustCrypto | enabled | 120.04 | 124.62 | +3.8% |
| SSE4.2 | tiny-keccak | enabled | 122.01 | 124.61 | +2.1% |
| SSE4.2 | asm-keccak | enabled | 54.98 | 124.63 | +126.7% |
| AVX2 | RustCrypto | enabled | 62.77 | 62.40 | -0.6% |
| AVX2 | tiny-keccak | disabled | 61.20 | 62.31 | +1.8% |
| AVX2 | asm-keccak | enabled | 51.98 | 62.70 | +20.6% |
| AVX-512 | RustCrypto | enabled | 60.43 | 62.35 | +3.2% |
| AVX-512 | tiny-keccak | disabled | 63.85 | 63.21 | -1.0% |
| AVX-512 | asm-keccak | enabled | 47.12 | 62.33 | +32.3% |
| native | RustCrypto | enabled | 59.60 | 62.58 | +5.0% |
| native | tiny-keccak | disabled | 58.33 | 61.94 | +6.2% |
| native | asm-keccak | enabled | 46.15 | 63.19 | +36.9% |


## Ecrecover

Direct calls to evm2's public `Crypto::secp256k1_ecrecover` provider. This includes
ECDSA parsing, public-key recovery, serialization and address hashing, with EVM
dispatch and calldata excluded. Each provider's fastest confirmed median is shown.

| Recovery implementation | Time (µs) | Faster than k256 |
| --- | ---: | ---: |
| libsecp256k1 (C) | 38.35 | +30.3% |
| k256 (Rust) | 49.97 | — |

### Three-pass recovery confirmation

132 samples per build across three passes.

| Compiler target | Address Keccak | LLVM SLP | Recovery implementation | Time (µs) |
| --- | --- | --- | --- | ---: |
| SSE4.2 | tiny-keccak | enabled | k256 | 50.28 |
| SSE4.2 | asm-keccak | enabled | k256 | 49.97 |
| AVX-512 | asm-keccak | enabled | libsecp256k1 | 38.39 |
| native | RustCrypto | disabled | libsecp256k1 | 38.35 |
| native | tiny-keccak | disabled | libsecp256k1 | 38.36 |
| native | asm-keccak | enabled | libsecp256k1 | 38.35 |
| native | asm-keccak | disabled | libsecp256k1 | 38.39 |

### All recovery builds

44 samples per configuration. Percentages compare providers with matching
compiler target, address-hashing backend and SLP setting.

| Compiler target | Address Keccak | LLVM SLP | libsecp256k1 (µs) | k256 (µs) | libsecp256k1 faster |
| --- | --- | --- | ---: | ---: | ---: |
| SSE2 | RustCrypto | enabled | 38.55 | 50.41 | +30.8% |
| SSE2 | tiny-keccak | enabled | 38.50 | 50.84 | +32.1% |
| SSE2 | asm-keccak | enabled | 38.29 | 50.40 | +31.6% |
| SSE4.2 | RustCrypto | enabled | 38.39 | 49.87 | +29.9% |
| SSE4.2 | tiny-keccak | enabled | 38.45 | 50.13 | +30.4% |
| SSE4.2 | asm-keccak | enabled | 38.36 | 49.84 | +29.9% |
| AVX2 | RustCrypto | enabled | 38.41 | 49.88 | +29.9% |
| AVX2 | tiny-keccak | disabled | 38.47 | 51.53 | +33.9% |
| AVX2 | asm-keccak | enabled | 38.54 | 49.87 | +29.4% |
| AVX-512 | RustCrypto | enabled | 38.32 | 50.04 | +30.6% |
| AVX-512 | tiny-keccak | disabled | 38.24 | 51.32 | +34.2% |
| AVX-512 | asm-keccak | enabled | 38.31 | 50.07 | +30.7% |
| native | RustCrypto | enabled | 38.35 | 50.36 | +31.3% |
| native | tiny-keccak | disabled | 38.39 | 50.96 | +32.8% |
| native | asm-keccak | enabled | 38.23 | 50.51 | +32.1% |

[Full matrix measurements](data/raw-api-matrix.json).
