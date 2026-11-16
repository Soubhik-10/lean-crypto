//! Publication harness. Discovery never generates keys or starts measurements.
#[cfg(feature = "experimental-simd")]
mod batched;
#[path = "suite/fixtures.rs"]
mod fixtures;
mod reference;
#[path = "suite/sampling.rs"]
mod sampling;

use alloy_primitives::{B256, keccak256_uncached};
use fixtures::Fixtures;
use sampling::{Case, Measurement};
use serde::Serialize;
use std::{
    env,
    error::Error,
    fs,
    hint::black_box,
    io::{self, BufRead},
    path::PathBuf,
};

const HASH_SIZES: [usize; 14] = [
    0, 32, 44, 64, 68, 80, 84, 93, 135, 136, 137, 432, 1072, 4096,
];
type VerifyFn = fn(&B256, &B256, &[u8]) -> bool;
type SignFn = fn(&B256, &B256) -> lean_sphincs::Signature;
type KeyFn = fn(&B256) -> B256;

#[derive(Serialize)]
struct Build {
    assembly: bool,
    tiny: bool,
    keccak_backend: &'static str,
    ecrecover: &'static str,
    target_arch: &'static str,
    avx2: bool,
    avx512f: bool,
    paired_fors: bool,
    fors_batch_lanes: usize,
    wots_batch_lanes: usize,
    reference_batch_lanes: usize,
    experimental_adapter: bool,
}

fn build() -> Build {
    Build {
        assembly: cfg!(feature = "asm-keccak"),
        tiny: cfg!(feature = "tiny-keccak"),
        keccak_backend: if cfg!(feature = "asm-keccak") {
            "assembly"
        } else if cfg!(feature = "tiny-keccak") {
            "tiny"
        } else {
            "portable"
        },
        ecrecover: if cfg!(feature = "secp256k1") {
            "libsecp256k1"
        } else {
            "k256"
        },
        target_arch: env::consts::ARCH,
        avx2: cfg!(target_feature = "avx2"),
        avx512f: cfg!(target_feature = "avx512f"),
        paired_fors: cfg!(all(
            target_arch = "x86_64",
            target_feature = "sse2",
            not(target_feature = "avx2")
        )),
        fors_batch_lanes: if cfg!(all(target_arch = "x86_64", target_feature = "avx2")) {
            4
        } else if cfg!(all(target_arch = "x86_64", target_feature = "sse2")) {
            2
        } else {
            1
        },
        wots_batch_lanes: if cfg!(all(target_arch = "x86_64", target_feature = "avx2")) {
            4
        } else {
            1
        },
        reference_batch_lanes: reference_keccak::LANES,
        experimental_adapter: cfg!(feature = "experimental-simd"),
    }
}

struct Options {
    samples: usize,
    sample_ms: u64,
    warmup_ms: u64,
    seed: u64,
    extra_cases: usize,
    groups: Vec<String>,
    per_fixture: bool,
    describe: bool,
    run: bool,
    wait: bool,
    output: PathBuf,
    corpus: Option<PathBuf>,
}

impl Options {
    fn parse() -> Result<Self, Box<dyn Error>> {
        let mut result = Self {
            samples: 500,
            sample_ms: 200,
            warmup_ms: 500,
            seed: 20261115,
            extra_cases: 8,
            groups: vec!["macro".into()],
            per_fixture: false,
            describe: false,
            run: false,
            wait: false,
            output: "matrix.json".into(),
            corpus: None,
        };
        let mut args = env::args().skip(1);
        while let Some(argument) = args.next() {
            match argument.as_str() {
                "--bench" => {}
                "--samples" => result.samples = args.next().ok_or("missing samples")?.parse()?,
                "--sample-ms" => {
                    result.sample_ms = args.next().ok_or("missing sample duration")?.parse()?
                }
                "--warmup-ms" => result.warmup_ms = args.next().ok_or("missing warmup")?.parse()?,
                "--seed" => result.seed = args.next().ok_or("missing seed")?.parse()?,
                "--extra-cases" => {
                    result.extra_cases = args.next().ok_or("missing extra cases")?.parse()?
                }
                "--groups" => {
                    result.groups = args
                        .next()
                        .ok_or("missing groups")?
                        .split(',')
                        .map(str::to_owned)
                        .collect()
                }
                "--per-fixture" => result.per_fixture = true,
                "--describe" => result.describe = true,
                "--run" => result.run = true,
                "--wait-for-start" => result.wait = true,
                "--json" => result.output = args.next().ok_or("missing output")?.into(),
                "--corpus-json" => {
                    result.corpus = Some(args.next().ok_or("missing corpus path")?.into())
                }
                "--help" => {
                    println!(
                        "matrix --describe | --run --samples N --sample-ms N --warmup-ms N --seed N --extra-cases N --groups macro,batched,reject,hash --per-fixture --json FILE --corpus-json FILE --wait-for-start"
                    );
                    std::process::exit(0);
                }
                _ => return Err(format!("unknown argument: {argument}").into()),
            }
        }
        if !(5..=100_000).contains(&result.samples)
            || !(10..=60_000).contains(&result.sample_ms)
            || result.warmup_ms > 60_000
            || result.extra_cases > 256
        {
            return Err("invalid sampling or corpus bounds".into());
        }
        if result.groups.is_empty()
            || result.groups.iter().any(|g| {
                !["direct", "macro", "batched", "reject", "hash", "ecrecover"].contains(&g.as_str())
            })
        {
            return Err("groups must be direct,macro,batched,reject,hash or ecrecover".into());
        }
        if result.includes("batched") && !cfg!(feature = "experimental-simd") {
            return Err("batched requires the experimental-simd benchmark feature".into());
        }
        Ok(result)
    }

    fn includes(&self, group: &str) -> bool {
        self.groups.iter().any(|g| g == group)
    }
}

fn add<'a>(cases: &mut Vec<Case<'a>>, name: String, items: u64, operation: impl FnMut(usize) + 'a) {
    cases.push(Case {
        name,
        work_items: items,
        operation: Box::new(operation),
    });
}

fn native_sign(seed: &B256, message: &B256) -> lean_sphincs::Signature {
    lean_sphincs::sign(seed, message).expect("validated signing input")
}

fn cases<'a>(fixtures: &'a Fixtures, options: &Options) -> Vec<Case<'a>> {
    let mut cases = Vec::new();
    let first = &fixtures.inputs[0];
    if options.includes("direct") {
        add(
            &mut cases,
            "direct/lean-sphincs/verify".into(),
            1,
            move |i| {
                let input = &fixtures.inputs[i % fixtures.inputs.len()];
                black_box(lean_sphincs::verify(
                    black_box(&input.key),
                    black_box(&input.message),
                    black_box(input.signature.as_slice()),
                ));
            },
        );
        add(&mut cases, "direct/leanVM/verify".into(), 1, move |i| {
            let input = &fixtures.inputs[i % fixtures.inputs.len()];
            black_box(reference_sphincs::verify(
                black_box(&input.parsed_key),
                black_box(&input.message.0),
                black_box(&input.parsed_signature),
            ));
        });
        add(&mut cases, "direct/lean-sphincs/sign".into(), 1, move |i| {
            let input = &fixtures.inputs[i % fixtures.inputs.len()];
            let _ = black_box(lean_sphincs::sign(
                black_box(&input.seed),
                black_box(&input.message),
            ));
        });
        add(&mut cases, "direct/leanVM/sign".into(), 1, move |i| {
            let input = &fixtures.inputs[i % fixtures.inputs.len()];
            black_box(reference_sphincs::sign(
                black_box(&input.seed.0),
                black_box(&input.message.0),
            ));
        });
        add(
            &mut cases,
            "direct/lean-sphincs/key_gen".into(),
            1,
            move |i| {
                let input = &fixtures.inputs[i % fixtures.inputs.len()];
                black_box(lean_sphincs::key_gen(black_box(&input.seed)));
            },
        );
        add(&mut cases, "direct/leanVM/key_gen".into(), 1, move |i| {
            let input = &fixtures.inputs[i % fixtures.inputs.len()];
            black_box(reference_sphincs::key_gen(black_box(&input.seed.0)));
        });
    }
    #[cfg(feature = "experimental-simd")]
    if options.includes("batched") {
        add(
            &mut cases,
            "macro/batched/verify_wire/mixed".into(),
            1,
            move |i| {
                let input = &fixtures.inputs[i % fixtures.inputs.len()];
                black_box(batched::verify(
                    black_box(&input.key),
                    black_box(&input.message),
                    black_box(input.signature.as_slice()),
                ));
            },
        );
        add(&mut cases, "macro/batched/sign/mixed".into(), 1, move |i| {
            let input = &fixtures.inputs[i % fixtures.inputs.len()];
            black_box(batched::sign(
                black_box(&input.seed),
                black_box(&input.message),
            ));
        });
        add(
            &mut cases,
            "macro/batched/key_gen/mixed".into(),
            1,
            move |i| {
                let input = &fixtures.inputs[i % fixtures.inputs.len()];
                black_box(batched::key_gen(black_box(&input.seed)));
            },
        );
    }
    if options.includes("macro") {
        let scopes: Vec<_> = std::iter::once(("mixed".to_owned(), None))
            .chain(
                fixtures
                    .inputs
                    .iter()
                    .take(if options.per_fixture { 3 } else { 0 })
                    .enumerate()
                    .map(|(i, v)| (v.name.clone(), Some(i))),
            )
            .collect();
        for (scope, selected) in scopes {
            for (provider, call) in [
                ("native", lean_sphincs::verify as VerifyFn),
                ("reference", reference::verify as VerifyFn),
            ] {
                add(
                    &mut cases,
                    format!("macro/{provider}/verify_wire/{scope}"),
                    1,
                    move |i| {
                        let case = &fixtures.inputs[selected.unwrap_or(i % fixtures.inputs.len())];
                        black_box(call(
                            black_box(&case.key),
                            black_box(&case.message),
                            black_box(case.signature.as_slice()),
                        ));
                    },
                );
            }
            add(
                &mut cases,
                format!("macro/reference/verify_parsed/{scope}"),
                1,
                move |i| {
                    let case = &fixtures.inputs[selected.unwrap_or(i % fixtures.inputs.len())];
                    black_box(reference::verify_parsed(
                        black_box(&case.parsed_key),
                        black_box(&case.message.0),
                        black_box(&case.parsed_signature),
                    ));
                },
            );
            for (provider, call) in [
                ("native", native_sign as SignFn),
                ("reference", reference::sign as SignFn),
            ] {
                add(
                    &mut cases,
                    format!("macro/{provider}/sign/{scope}"),
                    1,
                    move |i| {
                        let case = &fixtures.inputs[selected.unwrap_or(i % fixtures.inputs.len())];
                        black_box(call(black_box(&case.seed), black_box(&case.message)));
                    },
                );
            }
            for (provider, call) in [
                ("native", lean_sphincs::key_gen as KeyFn),
                ("reference", reference::key_gen as KeyFn),
            ] {
                add(
                    &mut cases,
                    format!("macro/{provider}/key_gen/{scope}"),
                    1,
                    move |i| {
                        let case = &fixtures.inputs[selected.unwrap_or(i % fixtures.inputs.len())];
                        black_box(call(black_box(&case.seed)));
                    },
                );
            }
        }
    }
    if options.includes("macro") || options.includes("ecrecover") {
        let provider = evm2::precompiles::crypto();
        add(&mut cases, "macro/evm2/ecrecover".into(), 1, move |_| {
            black_box(provider.secp256k1_ecrecover(
                black_box(&fixtures.ec_signature),
                black_box(fixtures.ec_id),
                black_box(&fixtures.ec_message.0),
            ))
            .expect("validated recovery fixture");
        });
    }
    if options.includes("reject") {
        for (label, key, message, signature) in [
            ("late", &first.key, &first.message, fixtures.late.as_slice()),
            (
                "counter_mutation",
                &first.key,
                &first.message,
                fixtures.counter.as_slice(),
            ),
            (
                "fors_mutation",
                &first.key,
                &first.message,
                fixtures.fors.as_slice(),
            ),
            (
                "wrong_key",
                &fixtures.wrong_key,
                &first.message,
                first.signature.as_slice(),
            ),
            (
                "wrong_message",
                &first.key,
                &fixtures.wrong_message,
                first.signature.as_slice(),
            ),
            (
                "truncated",
                &first.key,
                &first.message,
                &first.signature[..7739],
            ),
            (
                "overlong",
                &first.key,
                &first.message,
                fixtures.overlong.as_slice(),
            ),
            ("empty", &first.key, &first.message, &[]),
        ] {
            for (provider, call) in [
                ("native", lean_sphincs::verify as VerifyFn),
                ("reference", reference::verify as VerifyFn),
            ] {
                add(
                    &mut cases,
                    format!("reject/{provider}/{label}"),
                    1,
                    move |_| {
                        black_box(call(
                            black_box(key),
                            black_box(message),
                            black_box(signature),
                        ));
                    },
                );
            }
        }
    }
    if options.includes("hash") {
        for size in HASH_SIZES {
            let input: Vec<u8> = (0..size)
                .map(|i| (i as u8).wrapping_mul(37).wrapping_add(11))
                .collect();
            assert_eq!(keccak256_uncached(&input).0, reference_keccak::hash(&input));
            let native = input.clone();
            add(&mut cases, format!("hash/native/{size}"), 1, move |_| {
                black_box(keccak256_uncached(black_box(&native)));
            });
            let reference = input.clone();
            add(&mut cases, format!("hash/reference/{size}"), 1, move |_| {
                black_box(reference_keccak::hash(black_box(&reference)));
            });
            let lanes = reference_keccak::LANES;
            let batch = input.repeat(lanes);
            let mut output = vec![0; lanes * 32];
            reference_keccak::hash_many(&batch, size, &mut output);
            for digest in output.chunks_exact(32) {
                assert_eq!(digest, keccak256_uncached(&input).as_slice());
            }
            // This reports throughput per input, not the latency of one standalone hash.
            add(
                &mut cases,
                format!("hash/reference_batch/{size}"),
                lanes as u64,
                move |_| {
                    reference_keccak::hash_many(black_box(&batch), size, black_box(&mut output));
                    black_box(&output);
                },
            );
        }
    }
    cases
}

#[derive(Serialize)]
struct Report<'a> {
    schema_version: u32,
    status: &'static str,
    build: Build,
    samples: usize,
    sample_ms: u64,
    warmup_ms: u64,
    seed: u64,
    corpus_names: Vec<&'a str>,
    measurements: &'a [Measurement],
    methodology: &'static str,
}

fn write_report(
    options: &Options,
    fixtures: &Fixtures,
    measurements: &[Measurement],
    complete: bool,
) {
    let report = Report {
        schema_version: 1,
        status: if complete { "complete" } else { "running" },
        build: build(),
        samples: options.samples,
        sample_ms: options.sample_ms,
        warmup_ms: options.warmup_ms,
        seed: options.seed,
        corpus_names: fixtures.inputs.iter().map(|v| v.name.as_str()).collect(),
        measurements,
        methodology: "Single-threaded; randomized interleaving of kernels within each sampling round. Fixture generation, cross-checks, warmup, calibration and checkpoint I/O excluded. Samples are batch averages, not individual-call latency. Raw outliers retained. Signature operations recompute from the seed. Wire APIs include decoding/serialization; parsed verification excludes decoding. Hash batch results are normalized per input. CPU-time ratios do not establish protocol gas costs.",
    };
    let target = if complete {
        options.output.clone()
    } else {
        options.output.with_extension("partial.json")
    };
    let temporary = target.with_extension("tmp");
    fs::write(&temporary, serde_json::to_vec_pretty(&report).unwrap()).unwrap();
    fs::rename(temporary, target).unwrap();
}

fn main() -> Result<(), Box<dyn Error>> {
    let options = Options::parse()?;
    if options.describe {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "schema_version": 1, "build": build(), "hash_sizes": HASH_SIZES,
                "macro_cases": if options.per_fixture { 29 } else { 8 },
                "batched_cases": if cfg!(feature = "experimental-simd") { 3 } else { 0 },
                "direct_cases": 6,
                "reject_cases": 16, "hash_cases": 42, "ecrecover_cases": 1
            }))?
        );
        return Ok(());
    }
    if !options.run {
        return Err("Measurements require --run; use --describe for discovery".into());
    }
    if options.wait {
        let line = io::stdin()
            .lock()
            .lines()
            .next()
            .ok_or("missing start signal")??;
        if line.trim() != "start" {
            return Err("invalid start signal".into());
        }
    }
    let fixtures = Fixtures::new(options.extra_cases);
    #[cfg(feature = "experimental-simd")]
    if options.includes("batched") {
        for input in &fixtures.inputs {
            assert_eq!(
                batched::key_gen(&input.seed),
                input.key,
                "batched key: {}",
                input.name
            );
            assert_eq!(
                batched::sign(&input.seed, &input.message),
                input.signature,
                "batched signature: {}",
                input.name
            );
            assert!(
                batched::verify(&input.key, &input.message, input.signature.as_slice()),
                "batched verify: {}",
                input.name
            );
        }
    }
    if let Some(path) = &options.corpus {
        let corpus: Vec<_> = fixtures.inputs.iter().map(|v| serde_json::json!({
            "name": v.name, "seed": format!("{:#x}", v.seed), "message": format!("{:#x}", v.message),
            "public_key": format!("{:#x}", v.key), "signature": format!("{:#x}", v.signature),
        })).collect();
        let hashes: Vec<_> = HASH_SIZES.iter().map(|&size| {
    let data: Vec<_> = (0..size).map(|i| (i as u8).wrapping_mul(37).wrapping_add(11)).collect();
    serde_json::json!({"bytes": size, "expected": format!("{:#x}", keccak256_uncached(data))})
}).collect();
        let encoded = serde_json::to_vec_pretty(&serde_json::json!({
            "cases": corpus, "hashes": hashes,
            "ecdsa": {
                "message": format!("{:#x}", fixtures.ec_message),
                "signature": format!("0x{}{:02x}", alloy_primitives::hex::encode(fixtures.ec_signature), fixtures.ec_id),
                "public_key": format!("0x{}", alloy_primitives::hex::encode(fixtures.ec_public_key)),
                "address_word": format!("0x{}", alloy_primitives::hex::encode(fixtures.ec_word)),
            }
        }))?;
        if path.exists() {
            if fs::read(path)? != encoded {
                return Err("corpus differs from the existing session".into());
            }
        } else {
            fs::write(path, encoded)?;
        }
    }
    let mut kernels = cases(&fixtures, &options);
    if kernels.is_empty() {
        return Err("no kernels selected".into());
    }
    let measurements = sampling::measure(
        &mut kernels,
        options.samples,
        options.sample_ms,
        options.warmup_ms,
        options.seed,
        |partial| write_report(&options, &fixtures, partial, false),
    );
    write_report(&options, &fixtures, &measurements, true);
    Ok(())
}
