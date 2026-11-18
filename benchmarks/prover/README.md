# Unmodified leanVM prover comparison

The Linux Bash runner compares stock `leanvm-cli` binaries. It does not replace
upstream signature algorithms, witness generation, hashing, proving or verification.
It requires the tools listed in [the suite guide](../SUITE.md#requirements).

| Revision | Git pin |
| --- | --- |
| Previous | `4937c851eafb9e93bc7436eebe9e6dc8ae4c227a` |
| Current | `6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b` |

Both revisions include [PR #758](https://github.com/leanEthereum/leanVM/pull/758).
The newer revision has changes to witness generation and proving; its native
`lean_sphincs/src` and `keccak256/src` trees are unchanged from the previous pin.
Stable and experimental are upstream implementation names.

## Plan and build

```sh
bash benchmarks/prover/run.sh plan
bash benchmarks/prover/run.sh build
```

Planning checks supported CPU/OS features and the process's physical-core
allocation. Compilation uses `cargo install --git ... --rev ... --locked` for
`leanvm-cli`, with optimization level 3, Thin LTO and one codegen unit. Cargo
manages its Git dependency cache; no sibling repository is needed. Each revision
and CPU target has a separate Cargo target directory and preserved binary hash.

Both prover implementations are compiled into the stock binary with default CLI
dependencies, including `aggregation/signers-cache`. `--prover stable` and
`--prover experimental` select the implementation at runtime; they are not Cargo
features. Build checks only call `--help` and never generate signatures or proofs.

The quick preset selects both revisions, both provers, one worker and up to
sixteen allowed physical cores, and these workloads:

| Workload | CLI arguments |
| --- | --- |
| 16 leanSPHINCS signatures | `aggregate --sphincs 16` |
| 128 leanXMSS signatures | `aggregate --xmss 128` |
| Recursive: 2 × 16 leanSPHINCS | `recursion --n 2 --xmss-per-leaf 0 --sphincs-per-leaf 16` |

On a machine with sixteen available cores this is 24 jobs. Smaller hosts adapt
the default worker counts. Explicit `--threads` values must fit the allocation.
The full preset adds larger/mixed inputs, deeper recursion and more worker counts.

Use `--target native`, `avx2`, `avx2-gfni` or `avx512`. Unsupported instruction
sets fail before execution; `avx2-gfni` explicitly enables GFNI, PCLMULQDQ and
VPCLMULQDQ. Build and run must use the same target and pinned compiler.

## Run

```sh
bash benchmarks/prover/run.sh run --execute --session benchmarks/results/my-prover-run
```

`--execute` is required before any fixture signing or proof generation. Separate
processes prepare deterministic signer caches; file hashes must match across
revisions before timing. The selected upstream prover receives
`LEANVM_NUM_THREADS` and one allowed logical CPU per physical core. Both variants
receive the same allocation, and cooperating native/prover runners share CPU locks.

Each job discards one stock warmup and records five proving passes by default.
The WHIR inverse-rate logarithm is fixed to 1. Change it explicitly with
`--log-inverse-rate`; both revisions receive the same value. `--repeat`,
`--threads`, `--provers`, `--revisions` and `--workloads` select a narrower scope.
The default per-job timeout is 900 seconds; `--timeout` changes it.

Proof timing includes the whole upstream aggregation call, including witness
generation. Recursive child proofs are prepared before the timed parent step.
The stock CLI verifies the final measured proof in quiet verification passes.
The collector preserves every printed proving pass at millisecond precision,
the reported verification mean, proof size, parent-process peak RSS and raw logs.
These timings do not measure network propagation, block building or finality.
Our crate has no aggregate prover.

Interrupted jobs retain their files. Resume verifies the same source, plan,
compiler, binaries, caches and completed raw-log hashes before skipping them:

```sh
bash benchmarks/prover/run.sh run --execute --session benchmarks/results/my-prover-run --resume
```

## Report

```sh
bash benchmarks/prover/run.sh report --session benchmarks/results/my-prover-run
bash benchmarks/prover/run.sh report --measurements benchmarks/archive/data/proving-measurements.json
```

Reporting never executes a prover. It writes complete variant/revision tables,
normalized measurement JSON and per-job means under the ignored results directory.
All samples and slower comparisons are retained. Proving values are means of the
printed passes; verification is the stock reported mean. Peak RSS includes the
parent's lifetime and excludes recursive child-process memory.

Published [results](../archive/PROVING_RESULTS.md) and [setup details](../archive/BENCHMARK_SETUP.md)
retain the original measured builds. The shell port does not revise those data.
Run synthetic setup checks with `bash benchmarks/suite/test_setup.sh`.
