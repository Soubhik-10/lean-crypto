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

These gas columns are CPU-time calibrations, not measured EVM gas consumption
or recommendations for consensus pricing. A native scheme has a specified
verification charge; slower machine code does not automatically consume more
gas. The 3,000 anchor is the Ecrecover precompile; 2,800 is the proposed native
EIP-8141 secp256k1 signature charge. The proposal currently derives its
leanSPHINCS price from Keccak-permutation work instead of this timing ratio.
See [the native-scheme proposal](https://github.com/ethereum/EIPs/pull/12616).

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

```powershell
$env:GOAMD64 = "v1"
$env:GOMAXPROCS = "1"
$env:CGO_ENABLED = "1"
Set-Location crypto/leansphincs
go test -c -o leansphincs.test.exe .
```

Run the following three times as separate processes, pinning each process to
logical CPU 8 at above-normal priority before benchmark sampling:

```powershell
.\leansphincs.test.exe '-test.run=^$' '-test.bench=^(BenchmarkVerify|BenchmarkEcrecover|BenchmarkP256Verify|BenchmarkSign|BenchmarkKeyGen)$' -test.benchtime=2s -test.count=3 -test.cpu=1 -test.benchmem
```

Repeat with `CGO_ENABLED=0`, alternating configuration order as described above.
Run the executable from the package directory so its relative fixture paths resolve.

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
