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

fn measure(f: &mut impl FnMut()) -> f64 {
    let start = Instant::now();
    f();
    start.elapsed().as_secs_f64()
}

fn compare(name: &str, mut ours: impl FnMut(), mut reference: impl FnMut()) {
    ours();
    reference();
    let mut local = Vec::new();
    let mut upstream = Vec::new();
    for round in 0..5 {
        let (mut a, mut b) = (0.0, 0.0);
        for iteration in 0..30 {
            if (round + iteration) % 2 == 0 {
                a += measure(&mut ours);
                b += measure(&mut reference);
            } else {
                b += measure(&mut reference);
                a += measure(&mut ours);
            }
        }
        local.push(a / 30.0);
        upstream.push(b / 30.0);
    }
    local.sort_by(f64::total_cmp);
    upstream.sort_by(f64::total_cmp);
    println!(
        "{name}: local={:.3} ms reference={:.3} ms ratio={:.4}",
        local[2] * 1e3,
        upstream[2] * 1e3,
        local[2] / upstream[2]
    );
}

fn run_case(name: &str, verifier: &Verifier, expected: ReferenceClaims, reference: ReferenceProof) {
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
    compare(
        &format!("{name} verify"),
        || {
            assert_eq!(
                black_box(verifier).verify(black_box(&claims), black_box(&proof)),
                Ok(())
            )
        },
        || assert!(black_box(&reference).verify(black_box(&expected))),
    );
    compare(
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
}

fn main() {
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
    run_case("leaf", &verifier, leaf.0, leaf.1);
    run_case("recursive", &verifier, root.0, root.1);
}
