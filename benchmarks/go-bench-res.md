# Go leanSPHINCS: AMD64 benchmark results

Confirmation run: 18 November 2026. This is a native cryptographic-package
benchmark of the geth PoC, with the PR's benchmark functions and fixtures.

## Results

All figures are medians of nine retained repetitions per operation and
configuration: three fresh processes, with three two-second repetitions in
each process. Earlier samples are not pooled into this campaign.

| Operation | CGO_ENABLED=1 | CGO_ENABLED=0 | Unit |
| --- | ---: | ---: | --- |
| leanSPHINCS Verify | 130.525 | 133.878 | µs |
| Ecrecover | 28.755 | 109.749 | µs |
| P256 Verify | 49.228 | 49.360 | µs |
| leanSPHINCS Sign | 195.271 | 198.354 | ms |
| leanSPHINCS KeyGen | 69.082 | 69.699 | ms |

With cgo enabled, Ecrecover uses C libsecp256k1. With cgo disabled it uses
geth's Go Decred implementation. leanSPHINCS and P256 verification use the same
implementations in both builds. **AMD64 Keccak assembly is enabled in both**;
`CGO_ENABLED=0` does not mean the `purego` build tag was set.

| Configuration | Verify / Ecrecover | Ratio × 3,000 gas | Ratio × 2,800 gas |
| --- | ---: | ---: | ---: |
| CGO_ENABLED=1 | 4.539x | 13618 | 12710 |
| CGO_ENABLED=0 | 1.220x | 3660 | 3416 |

## Gas references and CPU work

| Gas reference | Charge | Status and source |
| --- | ---: | --- |
| Ecrecover precompile | 3,000 | Existing precompile; [EIP-1108 calibration](https://eips.ethereum.org/EIPS/eip-1108#specification) |
| P256VERIFY precompile | 6,900 | [EIP-7951 gas schedule](https://eips.ethereum.org/EIPS/eip-7951#gas-schedule) |
| Native SECP256K1 signature | 2,800 | [Draft EIP-8141](https://eips.ethereum.org/EIPS/eip-8141) |
| Native P256 signature | 6,700 | [Draft EIP-8141](https://eips.ethereum.org/EIPS/eip-8141) |
| Native leanSPHINCS signature | 12,600 | [Draft PR #12616](https://github.com/ethereum/EIPs/pull/12616), older 492-permutation pin |
| Updated leanSPHINCS price | 13,200 | [Review suggestion](https://github.com/ethereum/EIPs/pull/12616#pullrequestreview-5920543343) for 515 permutations |

These are verification charges, excluding signature-data costs and other
transaction work. Draft and review prices are not finalized protocol rules.

CPU time is the measured proxy for computational work on this machine.
The work ratio is `verify_time / reference_time`; it is not a ratio of CPU
clock speeds or a measure of the whole machine's computing capacity.

```text
work_ratio = verify_time / reference_time
gas_per_microsecond = reference_gas / reference_time_us
time_equivalent_gas = reference_gas * work_ratio
checks_per_second = 1,000,000,000 / median_ns_per_check
```

For the cgo-enabled Go run, verification takes **130.525 µs** and Ecrecover
**28.755 µs**: **4.539x CPU time**. A 3,000-gas anchor therefore gives
**104.330 gas/µs** and **13618 time-equivalent gas**. The native
2,800-gas anchor gives **97.374 gas/µs** and **12710 gas**.

| Configuration | Signature checks/s/core | Ecrecover checks/s/core | CPU-time ratio |
| --- | ---: | ---: | ---: |
| cgo enabled | 7,661 | 34,777 | 4.539x |
| cgo disabled | 7,469 | 9,112 | 1.220x |

These rates are reciprocals of the median batch times, not measured node TPS
or an extrapolation to all sixteen cores. Use the fast production recovery
backend as well as the Go-only control; a slower baseline lowers the ratio
without speeding up leanSPHINCS.

To compare computational work with the proposed 12,600-gas charge, normalize
CPU time per gas against each recovery reference:

```text
charge_ratio = 12600 / reference_gas
relative_cpu_time_per_gas = work_ratio / charge_ratio
```

| Reference | Charged-gas ratio | Measured CPU-time ratio | Relative CPU time per gas |
| --- | ---: | ---: | ---: |
| Ecrecover precompile | 4.200x | 4.539x | 1.0808x |
| Native SECP256K1 | 4.500x | 4.539x | 1.0087x |

With the native 2,800-gas reference, 12,600 buys a **4.500x** charge ratio
against the measured **4.539x** time ratio. That is a point estimate of
**0.87% more CPU time per gas**. Using the 3,000-gas
precompile reference instead gives **8.08% more**.
The small native-reference difference should not be interpreted as a precise
underpricing finding: sampling variation and operation boundaries also matter.
Geth's recovery benchmark returns a public key without address hashing.

P256 is a separate cross-check: 49.228 µs at the 6,900-gas reference gives
140.164 gas/µs and about 18295 equivalent gas for this
Go verifier. Its difference from the Ecrecover estimate demonstrates why a
single timing calibration cannot determine a network-wide gas price.

The measured format uses 515 permutations, while PR #12616's 12,600 price
still references the older 492-permutation format. Applying that proposal's
25.5-gas-per-permutation rule gives 13,132.5, rounded to the suggested 13,200.
The format pin must also be aligned before integration.

These calculations are local CPU-time comparisons, not measured EVM gas.
Native verification uses a specified charge; slower code does not consume
additional gas automatically. Signature data, transaction handling, client
differences and other CPU architectures require separate evaluation.

From this repository's root, recompute the Ecrecover calibration with `jq`:

```sh
jq '.summary["1"] |
    .operations.BenchmarkVerify.median_ns as $verify |
    .operations.BenchmarkEcrecover.median_ns as $ec |
    {cpu_time_ratio: ($verify / $ec),
     equivalent_gas_3000: (3000 * $verify / $ec),
     equivalent_gas_2800: (2800 * $verify / $ec),
     relative_cpu_time_per_gas_12600_native: (($verify / $ec) / (12600 / 2800)),
     checks_per_second: (1e9 / $verify)}' benchmarks/go-bench-2026-11-18.json
```

## Source and PR links

- [geth leanSPHINCS PoC, PR #36137](https://github.com/ethereum/go-ethereum/pull/36137).
- [Measured leanSPHINCS package at the pinned PR head](https://github.com/ethereum/go-ethereum/tree/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/crypto/leansphincs).
- [Exact benchmark functions and known-answer setup](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/crypto/leansphincs/leansphincs_test.go).
- [Pinned go.mod](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/go.mod) and [go.sum](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/go.sum).
- [AMD64 Keccak assembly](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/crypto/keccak/keccakf_amd64.s) and [its build selector](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/crypto/keccak/keccakf_amd64.go).
- [C-backed Ecrecover wrapper](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/crypto/signature_cgo.go) and [Go Ecrecover wrapper](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/crypto/signature_nocgo.go).
- [P256 benchmark input fixture](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/core/vm/testdata/precompiles/p256Verify.json).

PR head: `3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1`. PR base:
`142458d3dafaa05f013eee70703b280641780612`. The PR was open at the source check for this
campaign; these results do not establish an integration into mainnet geth.

The existing local geth checkout was reused at
`14f4be01e9d24659bc241922b2e43beba685554f`.
The PR package files were copied verbatim into benchmark scratch space.
The local checkout's module files and three root crypto files differ from the
PR, so this confirmation uses the PR's exact `go.mod`/`go.sum` via `-modfile`
and a Go build overlay for:

```text
crypto/keccak.go
crypto/keccak_cache.go
crypto/signature_nocgo.go
```

The local `common`, `crypto/keccak`, `crypto/secp256k1` and `crypto/secp256r1`
source trees match the PR base. Their tree hashes, the pinned-file SHA-256
hashes, build commands, selected source files and binary hashes are in the
raw data. The overlay leaves the existing checkout's files unchanged.

The PR contains a cache for its convenience `Keccak256` helpers. The timed
leanSPHINCS functions use `NewKeccakState` and hash directly, bypassing that
cache. Ecrecover returns a public key and does not hash an Ethereum address.
These timings therefore do not measure repeated-message cache hits.

## Machine and build setup

| Setting | Value |
| --- | --- |
| CPU | AMD Ryzen 9 8940HX; 16 cores, 32 logical processors |
| OS | Windows, amd64 |
| Go | go version go1.27.3 windows/amd64 |
| Go CPU target | GOAMD64=v1 |
| Go runtime parallelism | GOMAXPROCS=1 and -test.cpu=1 |
| C compiler for cgo | gcc (MinGW-W64 x86_64-ucrt-posix-seh, built by Brecht Sanders, r8) 13.2.0 |
| CGO_CFLAGS | `-O2 -g` |
| CGO_LDFLAGS | `-O2 -g` |
| Extra build tags | None; purego is not set |
| Affinity | Logical CPU 8, Windows affinity mask 0x100 |
| Process priority | Above normal |
| Power | AC power; existing Balanced power plan retained |
| SMT isolation | Sibling logical CPU 9 is not reserved |
| Clock / temperature | Not fixed or measured |
| Whole-system CPU utilization during processes | 4.43%–4.75%; retained in raw data |

The Go AMD64 target is explicitly recorded. The Rust report's native CPU
target and SIMD implementation differ, so raw Go-versus-Rust times do not
isolate the effect of the implementation language.

## Sampling and validation

- Both executables are freshly built with the pinned PR source overlay and
  module versions. Binary hashes are checked before execution.
- `TestKnownAnswer`, `TestRoundTrip`, `TestVerifyCost` and `TestMalformed`
  pass for both cgo configurations before timing. These cover the independent
  known-answer signature, round trips and every-byte mutation, malformed
  inputs, 515 permutations and the verification allocation bound.
- The PR's unchanged benchmark functions use `testing.B.Loop`; fixture loading,
  parsing for P256, and setup before the first Loop call are excluded from
  timed work. The Go benchmark framework performs its normal calibration.
- Each configuration runs in three fresh processes with three two-second
  repetitions per operation in each process. The order is cgo-on/off,
  off/on, then on/off, to alternate which configuration runs first.
- All 90 benchmark results are retained: five operations × nine repetitions
  × two configurations. Each reported statistic is a median of its nine
  ns/op values. No outliers are removed.
- The verification benchmark uses the PR's fixed known-answer input; Ecrecover
  and P256 use the PR's fixed fixtures. This is not a survey of arbitrary or
  adversarial signature inputs, an EVM VERIFY-frame run, or a block benchmark.

| Configuration | Operation | Minimum (µs) | Median (µs) | Maximum (µs) | Median B/op | Median allocs/op |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| cgo enabled | Verify | 129.780 | 130.525 | 133.005 | 1520 | 2 |
| cgo enabled | Ecrecover | 28.525 | 28.755 | 29.069 | 80 | 1 |
| cgo disabled | Verify | 132.632 | 133.878 | 135.428 | 1520 | 2 |
| cgo disabled | Ecrecover | 108.523 | 109.749 | 110.570 | 1512 | 27 |

Minimum and maximum describe the retained two-second throughput measurements,
not individual-call latency percentiles. The raw logs retain every iteration
count and the per-repetition byte/allocation figures for all five operations.

## Reproduction

From an existing geth checkout at the pinned PR head above, set the environment
explicitly and build the benchmark executable. For the cgo configuration,
provide a working C compiler and record its version and flags:

```sh
export GOAMD64=v1
export GOMAXPROCS=1
export GOFLAGS=''
cd crypto/leansphincs
CGO_ENABLED=1 go test -c -o leansphincs-cgo1-bench .
CGO_ENABLED=0 go test -c -o leansphincs-cgo0-bench .
```

The loop runs three fresh processes per configuration in the recorded
1/0, 0/1, 1/0 order. Match the recorded CPU affinity and priority when
reproducing on the same OS:

```sh
for cgo in 1 0 0 1 1 0; do
    "./leansphincs-cgo${cgo}-bench" '-test.run=^$' \
        '-test.bench=^(BenchmarkVerify|BenchmarkEcrecover|BenchmarkP256Verify|BenchmarkSign|BenchmarkKeyGen)$' \
        -test.benchtime=2s -test.count=3 -test.cpu=1 -test.benchmem
done
```

Run the executables from the package directory so their relative fixture paths
resolve. The examples use shell syntax; Windows Bash/MSYS2 can use the native
Windows Go toolchain. Linux or WSL builds use a different platform and should
be recorded as a separate campaign. The published measurements remain native
Windows results.

This campaign built against the existing checkout using `go test -c` with
`-mod=readonly`, `-modfile=<PR-module-file>` and `-overlay=<overlay.json>`,
followed by the six verbatim package `.go` paths. `-buildvcs=false` and
`-vet=off` were build-only options. Exact argument arrays and the source mapping
are retained in the raw JSON. Canonical package builds at the pinned PR head
do not need the overlay.

## Raw results

[All process logs, 90 measurements, setup, selected backends, source hashes,
binary hashes and correctness output](go-bench-2026-11-18.json).

These are fresh results. Earlier local runs used the existing checkout's
module files and wrappers; they remain recorded in the earlier audit data and
are not pooled with this PR-pinned confirmation.
