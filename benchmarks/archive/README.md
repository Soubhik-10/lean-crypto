# Historical benchmark campaigns

These reports retain earlier implementations, configurations and measurement
boundaries. Use the [current results](../README.md) and [batching explanation](../BATCHING.md)
for the maintained summary. Historical datasets are not pooled with current runs.

| Report | Scope |
| --- | --- |
| [Native matrix](RAW_RESULTS.md) | Full target/backend sweep and confirmations |
| [Proving](PROVING_RESULTS.md) | Upstream stable/experimental provers and recursion |
| [Setup](BENCHMARK_SETUP.md) | Exact setup for those native/proving campaigns |
| [SIMD confirmation](SIMD_RESULTS.md) | Local adapter over upstream primitives |
| [SIMD sweep](SIMD_SWEEP.md) | Earlier adapter and compiler experiments |
| [Initial measurements](INITIAL_RESULTS.md) | Earlier verifier and recovery comparisons |

All thirteen historical JSON files are preserved byte for byte under [data](data/).
Recorded source paths and hashes describe the original runs. Report-only commands
in [the suite](../SUITE.md#reports) accept the moved native/proving datasets.
