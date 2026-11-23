//! Compare matched admission, verification and optional proving with the reference.

use lean_aggregation::{Aggregate, Aggregator, B256, Claims, setup};
use lean_sphincs::{Signature, key_gen, sign};
use lean_vm::{AggregateClaims, AggregateProof, OutputClaims};
use std::{hint::black_box, time::Instant};

fn reference_input(
    key: &B256,
    message: &B256,
    signature: &Signature,
) -> Vec<(
    lean_vm::lean_sphincs::LeanSphincsPublicKey,
    [u8; 32],
    lean_vm::lean_sphincs::LeanSphincsSignature,
)> {
    assert!(lean_sphincs::verify(key, message, signature.as_slice()));
    vec![(
        lean_vm::lean_sphincs::LeanSphincsPublicKey::from_bytes(&key.0),
        message.0,
        lean_vm::lean_sphincs::LeanSphincsSignature::from_bytes(&signature.0),
    )]
}

fn measure(mut f: impl FnMut()) -> f64 {
    let start = Instant::now();
    f();
    start.elapsed().as_secs_f64()
}

fn compare<A, B>(name: &str, iterations: usize, mut adapter: A, mut reference: B)
where
    A: FnMut(),
    B: FnMut(),
{
    adapter();
    reference();
    let mut adapted = Vec::new();
    let mut direct = Vec::new();
    for sample in 0..5 {
        let (mut a, mut b) = (0.0, 0.0);
        for iteration in 0..iterations {
            // Pair adjacent calls so CPU frequency changes affect both sides.
            if (sample + iteration) % 2 == 0 {
                a += measure(&mut adapter);
                b += measure(&mut reference);
            } else {
                b += measure(&mut reference);
                a += measure(&mut adapter);
            }
        }
        adapted.push(a / iterations as f64);
        direct.push(b / iterations as f64);
    }
    adapted.sort_by(f64::total_cmp);
    direct.sort_by(f64::total_cmp);
    println!(
        "{name}: adapter={:.3} us reference={:.3} us ratio={:.4}",
        adapted[2] * 1e6,
        direct[2] * 1e6,
        adapted[2] / direct[2]
    );
}

fn main() {
    setup(4);
    let seed = B256::repeat_byte(11);
    let key = key_gen(&seed);
    let message = B256::repeat_byte(1);
    let signature = sign(&seed, &message).unwrap();
    let claims = Claims::new([(key, message)]);
    let native_claims = AggregateClaims {
        lean_sphincs: vec![(
            lean_vm::lean_sphincs::LeanSphincsPublicKey::from_bytes(&key.0),
            message.0,
        )],
        ..Default::default()
    };
    let mut inputs = Aggregator::with_capacity(1);
    inputs
        .add_signature(
            black_box(&key),
            black_box(&message),
            black_box(signature.as_slice()),
        )
        .unwrap();
    let proof = inputs.prove(None, 1).unwrap();
    let bytes = proof.to_bytes();
    let native = AggregateProof::from_bytes(&bytes).unwrap();
    assert!(native.verify(&native_claims));
    assert!(proof.verify(&claims));

    compare(
        "native admission and input conversion",
        1000,
        || {
            let mut inputs = Aggregator::with_capacity(1);
            inputs
                .add_signature(
                    black_box(&key),
                    black_box(&message),
                    black_box(signature.as_slice()),
                )
                .unwrap();
            black_box(inputs);
        },
        || {
            black_box(reference_input(
                black_box(&key),
                black_box(&message),
                black_box(&signature),
            ));
        },
    );
    compare(
        "aggregate verification",
        50,
        || assert!(black_box(&proof).verify(black_box(&claims))),
        || assert!(black_box(&native).verify(black_box(&native_claims))),
    );
    compare(
        "decode and verify",
        50,
        || {
            black_box(Aggregate::from_bytes(claims.clone(), black_box(&bytes)).unwrap());
        },
        || {
            let expected = native_claims.clone();
            let decoded = AggregateProof::from_bytes(black_box(&bytes)).unwrap();
            assert!(decoded.verify(&expected));
            black_box((expected, decoded));
        },
    );
    if std::env::args().any(|arg| arg == "--prove") {
        compare(
            "native admission and leaf proving",
            1,
            || {
                let mut inputs = Aggregator::with_capacity(1);
                inputs
                    .add_signature(
                        black_box(&key),
                        black_box(&message),
                        black_box(signature.as_slice()),
                    )
                    .unwrap();
                black_box(inputs.prove(None, 1).unwrap());
            },
            || {
                black_box(
                    lean_vm::aggregate(
                        &[],
                        vec![],
                        reference_input(
                            black_box(&key),
                            black_box(&message),
                            black_box(&signature),
                        ),
                        None,
                        OutputClaims::All,
                        1,
                    )
                    .unwrap(),
                );
            },
        );
    }
}
