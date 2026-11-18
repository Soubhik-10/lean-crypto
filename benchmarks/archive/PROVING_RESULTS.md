# leanVM proving results

Historical campaign. For the maintained summary, see [current Rust results](../README.md).

Unmodified upstream `leanvm-cli`, compiled with `target-cpu=native` on the same
AMD Ryzen 9 8940HX. Rust 1.97.1; LLVM 22.1.6; Linux GNU target under WSL2.
Optimization level 3, Thin LTO, one codegen unit. The CLI builds both prover
implementations; `--prover stable` or `--prover experimental` selects one at runtime.
Its upstream `aggregation/signers-cache` feature is enabled.

The current revision is [`6a828ecf`](https://github.com/leanEthereum/leanVM/tree/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b);
the previous pin is [`4937c851`](https://github.com/leanEthereum/leanVM/tree/4937c851eafb9e93bc7436eebe9e6dc8ae4c227a).
Both already include [PR #758](https://github.com/leanEthereum/leanVM/pull/758).
These are upstream implementation names, not production-readiness guarantees.
This crate has no aggregate prover; the following tables compare leanVM variants.
The CLI workloads execute the upstream verification programs.

Proving times are means of all five retained stock CLI passes after one warmup.
Pass times are printed to millisecond precision. Verification uses the CLI's
five-pass mean. WHIR `--log-inv-rate 1` is identical for every run. Recursive
times cover the parent proof over two children; constructing the child proofs
is excluded. Faster = `(baseline time / compared time − 1) × 100%`.
Negative values mean slower.

The experimental prover is faster in all six current workload/worker pairs.
The newer revision does not improve every proving case, and its proof-verification
times are higher in every measured pair below. These are observed timings;
small differences do not establish statistical significance.

## Current stable versus experimental

| Workload | Workers | Stable (s) | Experimental (s) | Experimental faster |
| --- | ---: | ---: | ---: | ---: |
| 16 leanSPHINCS signatures | 1 | 0.4904 | 0.3112 | +57.6% |
| 16 leanSPHINCS signatures | 16 | 0.1532 | 0.1054 | +45.4% |
| 128 leanXMSS signatures | 1 | 0.7440 | 0.4586 | +62.2% |
| 128 leanXMSS signatures | 16 | 0.1952 | 0.1420 | +37.5% |
| Recursive: 2 × 16 leanSPHINCS | 1 | 1.0508 | 0.6798 | +54.6% |
| Recursive: 2 × 16 leanSPHINCS | 16 | 0.3010 | 0.1910 | +57.6% |

## Previous versus current revision

| Workload | Workers | Prover | Previous (s) | Current (s) | Current faster |
| --- | ---: | --- | ---: | ---: | ---: |
| 16 leanSPHINCS signatures | 1 | stable | 0.4702 | 0.4904 | -4.1% |
| 16 leanSPHINCS signatures | 1 | experimental | 0.3018 | 0.3112 | -3.0% |
| 16 leanSPHINCS signatures | 16 | stable | 0.1466 | 0.1532 | -4.3% |
| 16 leanSPHINCS signatures | 16 | experimental | 0.1134 | 0.1054 | +7.6% |
| 128 leanXMSS signatures | 1 | stable | 0.7934 | 0.7440 | +6.6% |
| 128 leanXMSS signatures | 1 | experimental | 0.4804 | 0.4586 | +4.8% |
| 128 leanXMSS signatures | 16 | stable | 0.2028 | 0.1952 | +3.9% |
| 128 leanXMSS signatures | 16 | experimental | 0.1496 | 0.1420 | +5.4% |
| Recursive: 2 × 16 leanSPHINCS | 1 | stable | 1.1324 | 1.0508 | +7.8% |
| Recursive: 2 × 16 leanSPHINCS | 1 | experimental | 0.7656 | 0.6798 | +12.6% |
| Recursive: 2 × 16 leanSPHINCS | 16 | stable | 0.3006 | 0.3010 | -0.1% |
| Recursive: 2 × 16 leanSPHINCS | 16 | experimental | 0.2050 | 0.1910 | +7.3% |

## All proving measurements

| Revision | Workload | Workers | Prover | Proving (s) | Verification (ms) | Proof (KiB) | Peak RSS (GiB) |
| --- | --- | ---: | --- | ---: | ---: | ---: | ---: |
| previous | 16 leanSPHINCS signatures | 1 | stable | 0.4702 | 7.228 | 219.1 | 0.399 |
| previous | 16 leanSPHINCS signatures | 1 | experimental | 0.3018 | 7.299 | 219.1 | 0.413 |
| previous | 16 leanSPHINCS signatures | 16 | stable | 0.1466 | 7.386 | 219.1 | 0.484 |
| previous | 16 leanSPHINCS signatures | 16 | experimental | 0.1134 | 7.257 | 219.1 | 0.504 |
| previous | 128 leanXMSS signatures | 1 | stable | 0.7934 | 7.245 | 242.8 | 0.565 |
| previous | 128 leanXMSS signatures | 1 | experimental | 0.4804 | 6.972 | 242.8 | 0.585 |
| previous | 128 leanXMSS signatures | 16 | stable | 0.2028 | 7.765 | 242.8 | 0.681 |
| previous | 128 leanXMSS signatures | 16 | experimental | 0.1496 | 7.514 | 242.8 | 0.673 |
| previous | Recursive: 2 × 16 leanSPHINCS | 1 | stable | 1.1324 | 8.899 | 272.5 | 0.819 |
| previous | Recursive: 2 × 16 leanSPHINCS | 1 | experimental | 0.7656 | 8.895 | 272.5 | 0.841 |
| previous | Recursive: 2 × 16 leanSPHINCS | 16 | stable | 0.3006 | 9.804 | 272.5 | 0.917 |
| previous | Recursive: 2 × 16 leanSPHINCS | 16 | experimental | 0.2050 | 9.207 | 272.5 | 0.947 |
| current | 16 leanSPHINCS signatures | 1 | stable | 0.4904 | 8.975 | 219.1 | 0.399 |
| current | 16 leanSPHINCS signatures | 1 | experimental | 0.3112 | 9.865 | 219.1 | 0.415 |
| current | 16 leanSPHINCS signatures | 16 | stable | 0.1532 | 9.883 | 219.1 | 0.484 |
| current | 16 leanSPHINCS signatures | 16 | experimental | 0.1054 | 9.580 | 219.1 | 0.516 |
| current | 128 leanXMSS signatures | 1 | stable | 0.7440 | 9.932 | 244.7 | 0.553 |
| current | 128 leanXMSS signatures | 1 | experimental | 0.4586 | 9.576 | 244.7 | 0.577 |
| current | 128 leanXMSS signatures | 16 | stable | 0.1952 | 9.412 | 244.7 | 0.663 |
| current | 128 leanXMSS signatures | 16 | experimental | 0.1420 | 9.547 | 244.7 | 0.777 |
| current | Recursive: 2 × 16 leanSPHINCS | 1 | stable | 1.0508 | 12.382 | 271.0 | 0.803 |
| current | Recursive: 2 × 16 leanSPHINCS | 1 | experimental | 0.6798 | 11.818 | 271.0 | 0.831 |
| current | Recursive: 2 × 16 leanSPHINCS | 16 | stable | 0.3010 | 13.110 | 271.0 | 0.898 |
| current | Recursive: 2 × 16 leanSPHINCS | 16 | experimental | 0.1910 | 12.846 | 271.0 | 0.944 |

Peak RSS is the parent process lifetime peak; it excludes child-process memory.
[Setup and exact API boundaries](BENCHMARK_SETUP.md) ·
[Every proving sample and stock CLI report](data/proving-measurements.json).
