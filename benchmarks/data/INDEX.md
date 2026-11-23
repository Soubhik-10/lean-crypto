# Retained benchmark evidence

Files are preserved byte for byte from their published versions. Each dataset
records its own source revisions, build details and sampling boundaries.

| Dataset | Evidence |
| --- | --- |
| [Fresh native APIs](native-2026-11-23.json) | Linux/WSL lean-sphincs/leanVM/evm2 campaign; all 132 samples per operation and exact setup |
| [Aggregate verifier](verifier-2026-11-23.json) | CPU-pinned default/assembly runs, all paired samples and source/build/proof fingerprints |
| [Native API confirmation](ecrecover-2026-11-18.json) | Rust API/recovery campaigns and their original controls |
| [Recovery backends](ecrecover-backend-audit-2026-11-18.json) | C compiler controls, k256 and 32 ECDSA fixtures |
| [leanVM versus evm2](leanvm-ecrecover-2026-11-18.json) | Six fresh processes and every retained sample |
| [Batching audit](optimization-audit-2026-11-18.json) | Ablations, backend swaps, all hash preimages and assembly evidence |
| [Go confirmation](go-bench-2026-11-18.json) | PR-pinned cgo/non-cgo runs; [separate report](../go-bench-res.md) |

[Historical datasets](../archive/data/) accompany the [archived reports](../archive/README.md).
Fresh generated reports belong in ignored `benchmarks/results/`; build caches
belong in ignored `benchmarks/build/` or Cargo target directories.
