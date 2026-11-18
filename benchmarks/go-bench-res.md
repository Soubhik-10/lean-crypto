# Go leanSPHINCS: AMD64 results

Measured 18 November 2026, AMD Ryzen 9 8940HX, Windows amd64, Go 1.27.3.
This benchmarks the geth leanSPHINCS PoC's unchanged cryptographic functions.

## Results

Medians of nine repetitions per operation/configuration: three fresh processes,
three two-second repetitions each. All 90 measurements are retained.

| Operation | CGO_ENABLED=1 | CGO_ENABLED=0 | Unit |
| --- | ---: | ---: | --- |
| Verify | 130.525 | 133.878 | µs |
| Ecrecover | 28.755 | 109.749 | µs |
| P256 verify | 49.228 | 49.360 | µs |
| Sign | 195.271 | 198.354 | ms |
| Key generation | 69.082 | 69.699 | ms |
| Verify / Ecrecover | 4.539x | 1.220x | ratio |

Both modes use AMD64 Keccak assembly. Disabling cgo selects Go/Decred recovery;
it does not disable assembly. The cgo-enabled reference uses C libsecp256k1.
The slower Go-only recovery denominator lowers the ratio without accelerating
leanSPHINCS. No `purego` build tag is used.

## Gas calibration

Using [3,000 gas for Ecrecover](https://eips.ethereum.org/EIPS/eip-1108#specification),
the cgo-enabled ratio gives **13,618 time-equivalent gas**. At
[draft 8141's native 2,800-gas reference](https://eips.ethereum.org/EIPS/eip-8141),
it gives **12,710**. Against the [draft 12,600-gas leanSPHINCS charge](https://github.com/ethereum/EIPs/pull/12616),
that is 1.0087x the native recovery reference's CPU time per gas. This small
difference is not a precise pricing verdict.

```text
work_ratio = verify_time / recovery_time
time_equivalent_gas = reference_gas * work_ratio
relative_cpu_time_per_gas = work_ratio / (12600 / reference_gas)
```

The cgo-enabled medians correspond to approximately 7,661 signature checks/s/core
and 34,777 recoveries/s/core. These are throughput reciprocals, not node TPS.
Geth's recovery benchmark returns a public key without Ethereum address hashing.
Transaction work and data costs are excluded. Native verification has a fixed
charge; elapsed time does not automatically consume additional gas.

The measured format has 515 permutations. PR #12616's older 492-permutation pin
and 12,600 price need to be distinguished from the
[suggested 13,200-gas update](https://github.com/ethereum/EIPs/pull/12616#pullrequestreview-5920543343).

## Source and setup

- [geth PR #36137](https://github.com/ethereum/go-ethereum/pull/36137).
- [Pinned package and benchmarks](https://github.com/ethereum/go-ethereum/tree/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/crypto/leansphincs).
- [PR go.mod](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/go.mod) and [go.sum](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/go.sum).
- [AMD64 Keccak assembly](https://github.com/ethereum/go-ethereum/blob/3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1/crypto/keccak/keccakf_amd64.s).

| Setting | Value |
| --- | --- |
| PR head / base | `3ab7560bd2bf5bae47b4cafdf76c4f5c04b25cd1` / `142458d3dafaa05f013eee70703b280641780612` |
| Existing geth checkout | `14f4be01e9d24659bc241922b2e43beba685554f` |
| CPU target / parallelism | GOAMD64=v1; GOMAXPROCS=1; -test.cpu=1 |
| C compiler / flags | MinGW GCC 13.2.0; CGO_CFLAGS and CGO_LDFLAGS `-O2 -g` |
| Affinity / priority | Logical CPU 8 (mask 0x100); AboveNormal |
| Power / isolation | AC, Balanced policy; sibling CPU 9 not reserved |
| Frequency / temperature | Not fixed or measured |

The PR's six package files were built unchanged in scratch space against the
existing checkout. Exact PR module files are supplied with `-modfile`, and a
Go overlay supplies PR versions of `crypto/keccak.go`, `crypto/keccak_cache.go`
and `crypto/signature_nocgo.go`. The local `common`, `crypto/keccak`,
`crypto/secp256k1` and `crypto/secp256r1` source trees match the PR base.
No checkout files are changed. Exact mappings, commands, tree hashes and binary
hashes are in the raw data.

The PR's convenience hashing cache is bypassed: timed leanSPHINCS operations use
`NewKeccakState`. Known-answer, roundtrip/every-byte mutation, malformed-input
and 515-permutation tests pass for both modes. Go's normal calibration and
`testing.B.Loop` exclude fixture preparation from timing. Configuration order
alternates 1/0, 0/1, 1/0. These fixed-fixture package measurements do not cover
adversarial inputs, EVM execution or other CPU architectures.

## Reproduction

From an existing checkout at the pinned PR head, provide the recorded toolchains
and match CPU affinity/priority. A canonical package build does not need the
scratch overlay used by this campaign.

```sh
export GOAMD64=v1 GOMAXPROCS=1 GOFLAGS=''
cd crypto/leansphincs
CGO_ENABLED=1 go test -c -o leansphincs-cgo1-bench .
CGO_ENABLED=0 go test -c -o leansphincs-cgo0-bench .

for cgo in 1 0 0 1 1 0; do
    "./leansphincs-cgo${cgo}-bench" '-test.run=^$' \
        '-test.bench=^(BenchmarkVerify|BenchmarkEcrecover|BenchmarkP256Verify|BenchmarkSign|BenchmarkKeyGen)$' \
        -test.benchtime=2s -test.count=3 -test.cpu=1 -test.benchmem
done
```

Run from the package directory so relative fixtures resolve. Windows Bash/MSYS2
can use the native Windows toolchain. Linux/WSL builds are separate campaigns.

The measured scratch build used `go test -c -mod=readonly` with the PR module
files, overlay and six explicit `.go` paths; `-buildvcs=false` and `-vet=off`
were build-only options. Exact argument arrays are retained below.

[All 90 measurements, process logs, setup, source hashes and correctness output](data/go-bench-2026-11-18.json).
