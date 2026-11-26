//! Matched full verification, including deferred evaluation, against the pinned reference.

use lean_verifier::{AggregateClaims, AggregateProof, B256, Verifier};
use lean_vm::{AggregateClaims as ReferenceClaims, AggregateProof as ReferenceProof, OutputClaims};
use std::{hint::black_box, time::Instant};

fn signature(
    message: u8,
) -> (
    lean_vm::lean_sphincs::LeanSphincsPublicKey,
    [u8; 32],
    lean_vm::lean_sphincs::LeanSphincsSignature,
) {
    let seed = B256::repeat_byte(61);
    let message = B256::repeat_byte(message);
    let key = lean_sphincs::key_gen(&seed);
    let sig = lean_sphincs::sign(&seed, &message).unwrap();
    (
        lean_vm::lean_sphincs::LeanSphincsPublicKey::from_bytes(&key.0),
        message.0,
        lean_vm::lean_sphincs::LeanSphincsSignature::from_bytes(&sig.0),
    )
}

#[derive(serde::Serialize)]
struct Sample {
    round: usize,
    iteration: usize,
    local_first: bool,
    local_ns: u64,
    reference_ns: u64,
}

#[derive(serde::Serialize)]
struct Case {
    name: String,
    proof_bytes: usize,
    proof_keccak256: String,
    retained_sphincs_claims: usize,
    samples: Vec<Sample>,
}

struct Config {
    json: bool,
    rounds: usize,
    iterations: usize,
}

impl Config {
    fn parse() -> Self {
        let mut config = Self {
            json: false,
            rounds: 5,
            iterations: 30,
        };
        let mut args = std::env::args().skip(1);
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--json" => config.json = true,
                "--bench" => {} // Cargo's custom-harness marker.
                "--rounds" => {
                    config.rounds = args
                        .next()
                        .expect("round count")
                        .parse()
                        .expect("integer rounds")
                }
                "--iterations" => {
                    config.iterations = args
                        .next()
                        .expect("iteration count")
                        .parse()
                        .expect("integer iterations")
                }
                "--help" | "-h" => {
                    println!("verify [--json] [--rounds N] [--iterations N]");
                    std::process::exit(0);
                }
                _ => panic!("unknown option: {arg}"),
            }
        }
        assert!((1..=99).contains(&config.rounds), "rounds must be 1..99");
        assert!(
            (1..=10_000).contains(&config.iterations),
            "iterations must be 1..10000"
        );
        config
    }
}

fn measure(f: &mut impl FnMut()) -> u64 {
    let start = Instant::now();
    f();
    start
        .elapsed()
        .as_nanos()
        .try_into()
        .expect("duration fits u64")
}

fn median(mut values: Vec<f64>) -> f64 {
    values.sort_by(f64::total_cmp);
    let n = values.len();
    (values[(n - 1) / 2] + values[n / 2]) / 2.0
}

fn compare(
    config: &Config,
    name: &str,
    mut ours: impl FnMut(),
    mut reference: impl FnMut(),
) -> Vec<Sample> {
    ours();
    reference();
    let mut samples = Vec::with_capacity(config.rounds * config.iterations);
    for round in 0..config.rounds {
        for iteration in 0..config.iterations {
            let local_first = (round + iteration) % 2 == 0;
            let (local_ns, reference_ns) = if local_first {
                (measure(&mut ours), measure(&mut reference))
            } else {
                let reference_ns = measure(&mut reference);
                (measure(&mut ours), reference_ns)
            };
            samples.push(Sample {
                round,
                iteration,
                local_first,
                local_ns,
                reference_ns,
            });
        }
    }
    if !config.json {
        let local = median(
            samples
                .chunks(config.iterations)
                .map(|round| {
                    round.iter().map(|s| s.local_ns as f64).sum::<f64>() / config.iterations as f64
                })
                .collect(),
        );
        let upstream = median(
            samples
                .chunks(config.iterations)
                .map(|round| {
                    round.iter().map(|s| s.reference_ns as f64).sum::<f64>()
                        / config.iterations as f64
                })
                .collect(),
        );
        println!(
            "{name}: local={:.3} ms reference={:.3} ms ratio={:.4}",
            local / 1e6,
            upstream / 1e6,
            local / upstream
        );
    }
    samples
}

fn run_case(
    config: &Config,
    name: &str,
    verifier: &Verifier,
    expected: ReferenceClaims,
    reference: ReferenceProof,
) -> Vec<Case> {
    let claims = AggregateClaims {
        lean_sphincs: expected
            .lean_sphincs
            .iter()
            .map(|(key, message)| (B256::new(key.to_bytes()), B256::new(*message)))
            .collect(),
        ..Default::default()
    };
    let bytes = reference.to_bytes();
    let proof = AggregateProof::from_bytes(&bytes).unwrap();
    assert_eq!(verifier.verify(&claims, &proof), Ok(()));
    assert!(reference.verify(&expected));
    let verify = compare(
        config,
        &format!("{name} verify"),
        || {
            assert_eq!(
                black_box(verifier).verify(black_box(&claims), black_box(&proof)),
                Ok(())
            )
        },
        || assert!(black_box(&reference).verify(black_box(&expected))),
    );
    let decode = compare(
        config,
        &format!("{name} decode + verify"),
        || {
            let proof = AggregateProof::from_bytes(black_box(&bytes)).unwrap();
            assert_eq!(verifier.verify(black_box(&claims), &proof), Ok(()));
        },
        || {
            let proof = ReferenceProof::from_bytes(black_box(&bytes)).unwrap();
            assert!(proof.verify(black_box(&expected)));
        },
    );
    [
        (format!("{name} verify"), verify),
        (format!("{name} decode + verify"), decode),
    ]
    .into_iter()
    .map(|(name, samples)| Case {
        name,
        proof_bytes: bytes.len(),
        proof_keccak256: alloy_primitives::keccak256(&bytes).to_string(),
        retained_sphincs_claims: claims.lean_sphincs.len(),
        samples,
    })
    .collect()
}

fn main() {
    let config = Config::parse();
    lean_vm::setup(4);
    let verifier =
        Verifier::new(reference_aggregation::unified_guest().stacked_bytecode()).unwrap();
    let leaf = lean_vm::aggregate(
        &[],
        vec![],
        vec![signature(1), signature(2)],
        None,
        OutputClaims::All,
        1,
    )
    .unwrap();
    let kept = ReferenceClaims {
        lean_sphincs: vec![leaf.0.lean_sphincs[0]],
        ..Default::default()
    };
    let root = lean_vm::aggregate(
        std::slice::from_ref(&leaf),
        vec![],
        vec![],
        None,
        OutputClaims::Only(&kept),
        1,
    )
    .unwrap();
    let mut cases = run_case(&config, "leaf", &verifier, leaf.0, leaf.1);
    cases.extend(run_case(&config, "recursive", &verifier, root.0, root.1));
    if config.json {
        serde_json::to_writer(
            std::io::stdout().lock(),
            &serde_json::json!({
                "schema_version": 1,
                "reference_revision": lean_verifier::REFERENCE_REVISION,
                "rounds": config.rounds,
                "iterations": config.iterations,
                "log_inverse_rate": 1,
                "leaf_signature_count": 2,
                "cases": cases,
            }),
        )
        .expect("write raw benchmark samples");
        println!();
    }
}
