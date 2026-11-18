# Benchmark setup

## Source revisions

| Component | Source used for these measurements |
| --- | --- |
| lean-sphincs library and Rust harness | [`9d48d700`](https://github.com/Soubhik-10/lean-sphincs/tree/9d48d7004cef195fc0558b4c41bd72599db5eb8b) |
| leanVM, current | [`6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b`](https://github.com/leanEthereum/leanVM/tree/6a828ecf5b17d0dde4a38bf21d4e14b81d2d7f3b) |
| leanVM, previous proving control | [`4937c851eafb9e93bc7436eebe9e6dc8ae4c227a`](https://github.com/leanEthereum/leanVM/tree/4937c851eafb9e93bc7436eebe9e6dc8ae4c227a) |
| evm2 | [`e681662b6d9ec59edafd112f7c8d64f49f1e6dd1`](https://github.com/alloy-rs/evm2/tree/e681662b6d9ec59edafd112f7c8d64f49f1e6dd1) |
| Alloy types and hashing | [`70a63bd609da78dcf03e593ae772fec883ce7768`](https://github.com/alloy-rs/core/tree/70a63bd609da78dcf03e593ae772fec883ce7768) |
| EthLib parameter set and fixtures | [`03547dd83f298a63e6dcceff0a0b75f6142490aa`](https://github.com/ethereum/EthLib/tree/03547dd83f298a63e6dcceff0a0b75f6142490aa/EthLib/Cryptography/Sphincs) |

The current leanVM revision is the upstream main commit checked for the published campaign.
It is 20 commits ahead of the previous pin. Both already include
[PR #758](https://github.com/leanEthereum/leanVM/pull/758), which introduced the
separate stable and experimental Rust provers. This is a comparison between two
post-merge revisions, not a before/after measurement of that PR.

The `crates/lean_sphincs/src` and `crates/keccak256/src` trees are identical
between these two leanVM revisions. The newer changes concern proving and
witness generation; they do not establish an improvement to native signatures.
Both signature libraries and both upstream prover implementations are unmodified.

The measured lean-sphincs library and Rust benchmark sources match the linked
source commit. Locally, both leanVM Git dependencies in the benchmark manifest
and lockfile were repinned to the current revision, and benchmark documentation
was edited. The raw datasets retain the exact measured source hashes and these
dependency overrides. The shell runner records new source and platform snapshots
for future campaigns; the historical datasets retain their original provenance.

## Hardware and compiler

CPU: AMD Ryzen 9 8940HX, 16 cores and 32 hardware threads.

Compiler: Rust 1.97.1, LLVM 22.1.6; optimization level 3, Thin LTO, one codegen
unit. The published native signatures and evm2 use `x86_64-pc-windows-msvc`. Proving uses
`x86_64-unknown-linux-gnu` under Ubuntu on WSL2, because the stock CLI uses Unix
memory reporting and jemalloc. These are separate measurement categories.

| README target | Rust compiler flag |
| --- | --- |
| SSE2 | `-C target-cpu=x86-64` |
| SSE4.2 | `-C target-cpu=x86-64-v2` |
| AVX2 | `-C target-cpu=x86-64-v3` |
| AVX-512 | `-C target-cpu=x86-64-v4` |
| native | `-C target-cpu=native` |

The names identify compiler targets; they do not imply that every operation uses
that instruction width. `native` enables this CPU's available extensions. For
proving this includes AVX2, AVX-512, GFNI, PCLMULQDQ and VPCLMULQDQ.

SLP is LLVM's automatic vectorization of independent scalar instructions.
`-C no-vectorize-slp` is applied to the entire final build, including Thin LTO,
in tiny-keccak AVX2, AVX-512 and native configurations to avoid the reproduced
compiler regression. The confirmation also includes native RustCrypto and
asm-keccak controls with this flag. Both libraries share the flags within a
binary; their explicit SIMD implementations remain enabled.

## Native signature APIs

Each implementation receives the same seeds and message digests. The positive
corpus contains three specification fixtures and eight additional deterministic
key/message pairs. Before timing, the harness compares public keys and encoded
signatures byte-for-byte and checks verification against the expected result.

| Operation | lean-sphincs call | Unmodified leanVM call |
| --- | --- | --- |
| Key generation | `lean_sphincs::key_gen(&seed)` | `reference_sphincs::key_gen(&seed.0)` |
| Signing | `lean_sphincs::sign(&seed, &message)` | `reference_sphincs::sign(&seed.0, &message.0)` |
| Verification | `lean_sphincs::verify(&key, &message, signature.as_slice())` | `reference_sphincs::verify(&parsed_key, &message.0, &parsed_signature)` |

The `reference_sphincs` alias refers to upstream leanVM's Rust `lean_sphincs`
package, not a VM execution or a binding. Verification input parsing for leanVM
happens before timing; this crate borrows the encoded signature. Signing and key
generation return their native types without extra timed serialization. Both
recompute from the seed on every call. This measures each native API's cost,
not an identical wire-format integration boundary.

| Hash label | lean-sphincs / Alloy selection | leanVM signature selection |
| --- | --- | --- |
| RustCrypto | Default Alloy Keccak-256 Rust implementation | Upstream `keccak256`; no hash-backend feature added |
| tiny-keccak | `alloy-primitives/tiny-keccak`, version 2.0.2 | Same upstream `keccak256` |
| asm-keccak | `lean-sphincs/asm-keccak`, forwarding to Alloy assembly hashing | Same upstream `keccak256` |

leanVM's signature and Keccak packages declare no optional Cargo features.
Their hashing implementation is selected by CPU compilation flags, including
its upstream AVX-512 single-state permutation in AVX-512 and native builds.
The separate upstream batched hashing API is not substituted into signature
functions. The raw metadata's `reference_batch_lanes` field records that API's
available width, not batching performed by these signature calls. Our crate's
internal SIMD runs as implemented in the library: two FORS lanes in SSE2 builds,
and four FORS/WOTS lanes when AVX2 is enabled.
`experimental-simd` is absent and the compiled `experimental_adapter` marker is
false in every measured binary. There are no locally added signature algorithms
or batching adapters on either side.

The full matrix has 30 CPU/hash/recovery configurations: 15 binaries containing
six signature cases and C recovery, and 15 binaries measuring Rust recovery
only. Each case has 44 retained samples in one pass. Signature samples rotate
over all 11 inputs with equal weight, and operation order is shuffled. Timed
batches target at least 10 ms after a 100 ms case warmup. The datasets preserve
elapsed nanoseconds, iteration counts, input denominators and sample ordering.
A sample is a batch average, not an individual operation's tail latency.

The matrix selects candidates using complete medians. A separate three-pass
confirmation measures those candidates plus the prepared compiler controls,
with 44 fresh samples per pass. Headline values select each implementation's
lowest complete 132-sample median for that operation. The matched rows show
both libraries under identical build flags. Matrix samples are not pooled into
confirmation results. All samples are retained; no fastest-pass selection or
outlier deletion is used. Small differences are not claims of statistical
significance or a universal performance limit.

## evm2 ECDSA recovery

The timed call is
`evm2::precompiles::crypto().secp256k1_ecrecover(sig, recovery_id, message)`.
The provider is initialized before timing. It performs signature parsing,
public-key recovery, serialization and address hashing. EVM dispatch, calldata
and transaction execution are excluded. One fixed valid ECDSA input is shared
across all configurations.

| Recovery label | Feature selection |
| --- | --- |
| libsecp256k1 | Benchmark `secp256k1`, forwarding to `evm2/secp256k1` |
| k256 | `--no-default-features`, leaving evm2's Rust recovery implementation |

Compiler target labels refer to Rust compilation. No per-target `CC`, `CFLAGS`,
`CXX` or `CXXFLAGS` overrides were set for the C dependency.

The address-hashing columns select Alloy's RustCrypto, tiny-keccak or asm-keccak
backend; the latter forwards through `evm2/asm-keccak`. Percentages compare
providers with matching target, hash and SLP settings in the full matrix.
The headline compares each provider's fastest independently confirmed build.
These CPU timings do not set a consensus gas schedule.

## Stock leanVM proving CLI

The measured package is upstream `leanvm-cli`, binary `leanvm`. Both stable and
experimental prover dependencies are compiled into the same binary with the
CLI's default dependency selection. `--prover stable` and
`--prover experimental` are runtime arguments, not Cargo features. The CLI
enables `aggregation/signers-cache` as specified upstream. These names do not
assert production readiness.

Both pinned revisions use the same native CPU flags and release profile.
Cargo target directories are isolated by revision. No local code changes the
upstream witness generator, prover, verifier or recursive aggregation.

| Workload | Stock CLI arguments |
| --- | --- |
| 16 leanSPHINCS signatures | `aggregate --sphincs 16` |
| 128 leanXMSS signatures | `aggregate --xmss 128` |
| Recursive: 2 × 16 leanSPHINCS | `recursion --n 2 --xmss-per-leaf 0 --sphincs-per-leaf 16` |

Every workload is measured with both provers, both revisions and 1 or 16 workers,
for 24 jobs. `LEANVM_NUM_THREADS` selects the worker count; both variants receive
the same CPU allocation, with one logical CPU per guest-reported physical core.
The WHIR inverse-rate logarithm is fixed with `--log-inv-rate 1` throughout.

Separate processes prepare deterministic signer caches before measured jobs.
Their complete file hashes match across revisions. This excludes key generation
and fixture signing from the measured process and avoids a second fixture-generation
thread pool in the older revision. The raw artifact retains the cache hashes.

Each stock CLI job discards one proving warmup and retains five proving passes.
The measured stage calls upstream `aggregate::<P>` and includes witness generation.
For recursion, child proofs are built before timing; only the parent aggregation
step is measured. The CLI verifies the resulting proof in five quiet verification
passes and asserts success. Verification is of the final measured proof, not
independent timing or verification of every intermediate proving pass.

Proving table values are arithmetic means of all five retained pass times,
which the CLI prints to millisecond precision. Four decimal places show the
mean's arithmetic, not extra precision for individual passes. Verification is
the upstream reported mean; the CLI does not expose its individual pass times.
Proof sizes are reported in KiB. Peak RSS is the parent process lifetime maximum,
including its warmup and preparation, and excludes child-process RSS. It is not
a measurement of peak allocation within the timed stage alone.

The comparison measures proof generation and verification. It does not measure
network propagation, complete block building, or finality. lean-sphincs has no
aggregate prover, so there is no invented proving result for this crate.

## Reproduction and raw data

The Linux shell runner uses the same Rust benchmark kernels and the current
pinned dependencies. New Linux native runs use the GNU target and form a
separate campaign from the published Windows MSVC measurements. The historical
source snapshot and exact overrides above retain the original build provenance.
No sibling checkout is required.

```sh
bash benchmarks/run.sh build --profile raw --targets baseline,v2,v3,v4,native --hashing portable,tiny,assembly --recovery libsecp256k1,k256 --groups direct,ecrecover
bash benchmarks/run.sh run --profile raw --targets baseline,v2,v3,v4,native --hashing portable,tiny,assembly --recovery libsecp256k1,k256 --groups direct,ecrecover --passes 1
```

On Linux, build each unmodified CLI revision using its own Cargo target directory
and install prefix. For example, substitute `REV` with either full Git revision:

```sh
RUSTFLAGS="-C target-cpu=native" \
CARGO_PROFILE_RELEASE_OPT_LEVEL=3 \
CARGO_PROFILE_RELEASE_LTO=thin \
CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 \
CARGO_TARGET_DIR="target/prover-$REV" \
cargo +1.97.1 install leanvm-cli --git https://github.com/leanEthereum/leanVM \
  --rev "$REV" --locked --bin leanvm --root "build/prover-$REV"

LEANVM_NUM_THREADS=16 build/prover-$REV/bin/leanvm \
  --prover experimental --repeat 5 --cooldown 2 --log-inv-rate 1 \
  aggregate --sphincs 16
```

Prepare the matching signer caches outside the measured processes and use the
same CPU allocation for both variants. Every exact measured CLI argument list,
binary hash, lockfile hash, cache hash, proving sample and stock report is in
[proving-measurements.json](proving-measurements.json).

[Native matrix samples](raw-api-matrix.json) ·
[Native confirmation samples](raw-api-measurements.json) ·
[Native tables](RAW_RESULTS.md) · [Proving tables](PROVING_RESULTS.md).

Percent faster means `(baseline time / compared time − 1) × 100%`, calculated
from unrounded summary values. It describes an increase in operation rate;
percentage reduction in elapsed time is a different calculation. Negative
percentages and all slower configurations remain visible.
