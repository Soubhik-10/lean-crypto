# Rust benchmark results

## Latest Linux/WSL campaign — 23 November 2026

AMD Ryzen 9 8940HX, logical CPU 8, Linux/WSL2 x86_64, Rust 1.97.1 / LLVM
22.1.6, native CPU flags, thin LTO and one codegen unit. Signature/recovery
uses assembly Alloy Keccak and Clang 18.1.3 for the C recovery backend.

| Native API | lean-sphincs | Pinned leanVM | Speedup |
| --- | ---: | ---: | ---: |
| Verification | 38.56 µs | 128.86 µs | 3.34x |
| Signing | 93.23 ms | 127.25 ms | 1.36x |
| Key generation | 48.68 ms | 66.28 ms | 1.36x |

Native evm2 ecrecover is **26.69 µs** in the same campaign: our verification
uses 1.445x that CPU time and the reference uses 4.828x. This is the actual
C/libsecp256k1 provider, including compact signature recovery and address hashing.
All 132 samples per operation are retained across three fresh processes and
11 shared PQ fixtures. [Raw campaign and build metadata](data/native-2026-11-23.json).

The independent aggregate verifier's matching campaign uses three processes,
five rounds per process and 30 paired calls per round, retaining all 450 pairs
per workload/backend. The table uses assembly streaming hashes:

| Aggregate workload | lean-verifier (ms) | Pinned leanVM (ms) | Paired time reduction |
| --- | ---: | ---: | ---: |
| Leaf decoding + verification | 10.432 | 14.256 | 26.7% |
| Recursive decoding + verification | 14.951 | 20.017 | 25.0% |

Default hashing measured 10.425 / 14.318 ms and 14.828 / 19.876 ms,
respectively. The leaf contains two leanSPHINCS signatures; the recursive
parent retains one claim, at log-inverse-rate 1. Program preparation and
proving are untimed. [All paired samples](data/verifier-2026-11-23.json)
and [all four workloads](../crates/lean-verifier/README.md#validation-and-benchmarks).

```sh
bash benchmarks/compare.sh native --cpu 8 --cc clang --session benchmarks/results/signatures
bash benchmarks/compare.sh verifier --cpu 8 --session benchmarks/results/verifier
```

The signature reference remains `6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b`;
the aggregate verifier uses `84780fb42667bc288c0e567c125b7e10479fb568`.
Each comparison uses identical inputs within its own pinned protocol.
Exact source/binary fingerprints, flags and dependency features are retained.
Frequency and temperature are not fixed, and the SMT sibling is not reserved.
Compare paired implementations within each campaign; Windows and Linux absolute
timings are separate measurements. [Shell options](SUITE.md).

## Historical Windows campaign — 18 November 2026

Measured 18 November 2026 on an AMD Ryzen 9 8940HX (16 cores / 32 threads),
Windows x86-64 MSVC, Rust 1.97.1 / LLVM 22.1.6. These are native CPU timings.

### Run comparisons

```sh
bash benchmarks/compare.sh native --session benchmarks/results/native-comparison
bash benchmarks/compare.sh backends --session benchmarks/results/backend-comparison
bash benchmarks/compare.sh hashes --session benchmarks/results/hash-comparison
```

Each command builds, runs and reports its selected comparison. See the
[shell presets](SUITE.md#compare-ours-leanvm-and-ecrecover) for plan-only,
compiler/CPU selection, longer runs and resume. Requires Linux/WSL and the
[listed tools](SUITE.md#requirements).

### Native APIs

| Operation | lean-sphincs | Unmodified leanVM | Speedup |
| --- | ---: | ---: | ---: |
| Verification | 36.907 µs | 119.276 µs | 3.23x |
| Signing | 88.25 ms | 118.68 ms | 1.34x |
| Key generation | 46.34 ms | 61.49 ms | 1.33x |

Each row compares the two libraries within the same build and campaign.
Verification is from the [batching audit](BATCHING.md); signing/key generation
are from the earlier [native API confirmation](data/ecrecover-2026-11-18.json).
Campaigns are kept separate. Each uses three processes, 132 samples per
operation and eleven shared signature fixtures.

Both libraries use release optimization, native CPU features, Thin LTO and one
codegen unit. Our build enables Alloy's assembly Keccak. leanVM uses its own
native Keccak implementation, including AVX-512 on this machine. Our verifier
groups four independent hashes; [the audit](BATCHING.md) checks parameter
equivalence and isolates batching and hash-backend gains.

### evm2 recovery

The recovery-provider audit uses 32 deterministic ECDSA signatures and eleven
PQ fixtures, with three processes and 132 retained samples per configuration.

| Configuration | Our verify (µs) | evm2 ecrecover (µs) | Verify / ecrecover |
| --- | ---: | ---: | ---: |
| Assembly Keccak + Clang C/libsecp256k1 | 36.843 | 25.634 | 1.437x |
| RustCrypto Keccak + Rust k256 | 40.663 | 50.646 | 0.803x |

The C backend is evm2's actual default provider through secp256k1 0.33.1 /
secp256k1-sys 0.14.1, compiled with Clang-cl 21.1.8. The alternative provider
uses k256 0.14.0. The earlier MSVC C build took 38.387 µs for recovery; compiler
choice materially affects the ratio. Component checks put Clang recovery at
25.399 µs, signature parsing at 0.018 µs and address hashing at 0.170 µs.

[Backend audit: every sample, source and compiler metadata](data/ecrecover-backend-audit-2026-11-18.json).

A separate confirmation compares upstream leanVM directly with the same evm2
provider. It retains 132 samples per operation/configuration over three fresh
processes and uses the existing fixed ECDSA fixture, checked against the
32-input corpus above.

### leanVM and ecrecover

| evm2 recovery backend | leanVM verify (µs) | evm2 ecrecover (µs) | Ratio |
| --- | ---: | ---: | ---: |
| Clang C/libsecp256k1 | 121.076 | 25.545 | 4.740x |
| Rust k256 | 119.701 | 50.825 | 2.355x |

[Every confirmation sample and build hash](data/leanvm-ecrecover-2026-11-18.json).
One control process measured our verifier at 52.141 µs instead of about 37 µs.
All its samples remain included. The cause is unresolved; the six later
batching-audit processes did not reproduce it. See [limits](BATCHING.md#limits).

### Gas references

| Reference | Verification charge | Source |
| --- | ---: | --- |
| Ecrecover precompile | 3,000 | [EIP-1108 calibration](https://eips.ethereum.org/EIPS/eip-1108#specification) |
| Native SECP256K1 | 2,800 | [Draft EIP-8141](https://eips.ethereum.org/EIPS/eip-8141) |
| Native leanSPHINCS | 12,600 | [Draft PR #12616](https://github.com/ethereum/EIPs/pull/12616), older 492-permutation pin |
| Updated leanSPHINCS suggestion | 13,200 | [Review for the 515-permutation layout](https://github.com/ethereum/EIPs/pull/12616#pullrequestreview-5920543343) |

```text
cpu_time_ratio = verify_time / ecrecover_time
time_equivalent_gas = reference_gas * cpu_time_ratio
checks_per_second_per_core = 1,000,000 / median_microseconds
relative_cpu_time_per_gas = cpu_time_ratio / (scheme_gas / reference_gas)
```

The fast C recovery control calibrates our verifier to approximately **4,312
gas** at the 3,000-gas anchor, or **4,024** at 2,800. The separate upstream
leanVM confirmation gives **14,219** and **13,271**, respectively. For upstream,
12,600 gas corresponds to 1.0533x the local CPU time per gas of the 2,800-gas
recovery reference.

These are local runtime calibrations. Native verification has a fixed protocol
charge; the Rust call does not consume gas according to its elapsed time.
Transaction data, dispatch, bandwidth, adversarial inputs and other machines
require separate evaluation. The draft format pin and price must also agree.

### Setup

| Component | Revision / setting |
| --- | --- |
| leanVM | `6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b` |
| evm2 | `e681662b6d9ec59edafd112f7c8d64f49f1e6dd1` |
| Alloy core | `70a63bd609da78dcf03e593ae772fec883ce7768` |
| EthLib layout | `03547dd83f298a63e6dcceff0a0b75f6142490aa` |
| Rust flags | opt-level 3, target-cpu native, Thin LTO, one codegen unit |
| Process | CPU 8, AboveNormal priority, AC power, Balanced policy |

SMT sibling 9 is not reserved. Frequency and temperature are not fixed or
measured. Kernels warm up before timing, calibrate batches and randomize their
order within sampling rounds. Every sample is retained. Exact source/binary
hashes, commands and per-campaign settings are in the raw files.

Our verifier consumes signature bytes. Upstream receives keys/signatures parsed
before timing. evm2 includes compact-signature parsing, recovery, serialization
and address hashing; its provider is initialized before timing. No EVM dispatch
or aggregation proof work is included. Correctness checks and fixture setup are
outside the timed region.

Use the [shell suite](SUITE.md) for build/run/report commands. Published native
measurements used Windows; a fresh Linux/WSL run is a separate campaign.
[Raw-data index](data/INDEX.md) lists the retained datasets. [Archived reports](archive/README.md)
contain older matrices, prover measurements and implementation experiments.
