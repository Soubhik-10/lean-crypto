# evm2 comparison harness

This separate Cargo package calls
`evm2::precompiles::crypto().secp256k1_ecrecover` from the pinned Git dependency
`alloy-rs/evm2` at `e681662b6d9ec59edafd112f7c8d64f49f1e6dd1`.
The measured method includes compact r/s parsing, public-key recovery,
serialization, Keccak hashing, and construction of the padded address word.
Provider initialization and signing happen before measurement. This excludes
EVM interpreter dispatch and transaction data/intrinsic gas.

Alloy is pinned to `alloy-rs/core` at
`70a63bd609da78dcf03e593ae772fec883ce7768`. The registry patch makes evm2
use the same Git-sourced primitives as the verifier. No sibling repository is
required or accessed. The only path dependency is the verifier inside this
same repository.

The harness has its own manifest and lockfile. The core verifier's dependency
graph contains no evm2, libsecp256k1, benchmark framework, or fixture parser.

Run from the `lean-sphincs` repository:

```sh
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench verify -- \
  --samples 30 --sample-ms 100 --json benchmarks/portable.json
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench verify \
  --features asm-keccak -- \
  --samples 30 --sample-ms 100 --json benchmarks/asm-keccak.json
```

The default harness feature selects evm2's libsecp256k1 backend. With
`--no-default-features`, the evm2 provider uses its RustCrypto k256 fallback.
`--features asm-keccak` enables the same Alloy assembly backend for the verifier
and evm2's address hashing.

Each operation is warmed during adaptive batch calibration. The timer surrounds
whole batches, not individual calls. Thirty samples of at least 100 ms per
sample are the default. Values pass through `std::hint::black_box`. Valid
verification rotates all three positive reference cases. A separate late
rejection changes the last sibling byte, after all chain encodings remain
valid, exercising a full verification before rejecting.

JSON records compiler, CPU (set `BENCH_CPU` for the full model name), OS,
architecture, exact evm2 and Alloy Git sources, backend selection, iteration count,
all samples, median and p05/p95. Percentiles describe batch-average ns/op and
are not individual-call latency percentiles. Local gas estimates use ratios
of medians to the 3,000-gas ecrecover precompile and the 2,800-gas frame scheme.
They do not establish a consensus price or include signature-data costs.

## CodSpeed

The `codspeed` target uses the Git-pinned CodSpeed Divan compatibility layer.
It registers all three positive reference cases for signing and verification,
plus key generation, full-work late rejection, evm2 ecrecover and representative
64-, 80- and 1,072-byte Keccak inputs. Fixtures are validated before measurement.
Every signing/key-generation iteration computes its result from the secret seed;
no precomputed key or tree is substituted for the measured operation.

```sh
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench codspeed
cargo bench --manifest-path benchmarks/evm2/Cargo.toml --bench codspeed --features asm-keccak
```

CI measures RustCrypto and `asm-keccak` with both `target-cpu=x86-64` (SSE2)
and `target-cpu=x86-64-v3` (AVX2). The SSE2 series retain the `portable` and
`assembly` namespaces; AVX2 uses `portable_avx2` and `assembly_avx2`.
The benchmark checks the compiler's AVX2 selection at build time.
The workflow uses OIDC authentication and CodSpeed CPU simulation on Linux for
consistent regression comparisons. The existing wall-clock target remains the
source of local elapsed-time measurements and ecrecover-relative gas estimates.
