//! Native signature interoperability, exact coverage and recursive pruning.

use lean_aggregation::{
    Aggregate, AggregateError, Aggregator, B256, Claims, MAX_LOG_INV_RATE, MAX_RECURSIONS, setup,
};
use lean_sphincs::{Signature, key_gen, sign};
use lean_vm::{AggregateClaims, AggregateProof, OutputClaims};

fn signed(seed: u8, message: u8) -> (B256, B256, Signature) {
    let seed = B256::repeat_byte(seed);
    let message = B256::repeat_byte(message);
    (key_gen(&seed), message, sign(&seed, &message).unwrap())
}

fn reference_claims(claims: &Claims) -> AggregateClaims {
    AggregateClaims {
        lean_sphincs: claims
            .iter()
            .map(|(key, message)| {
                (
                    lean_vm::lean_sphincs::LeanSphincsPublicKey::from_bytes(&key.0),
                    message.0,
                )
            })
            .collect(),
        ..Default::default()
    }
}

#[test]
fn claims_use_reference_order_and_set_semantics() {
    let a = (B256::repeat_byte(1), B256::repeat_byte(9));
    let b = (B256::repeat_byte(2), B256::repeat_byte(0));
    let c = (a.0, B256::repeat_byte(8));
    let claims = Claims::new([b, a, c, b]);
    assert_eq!(claims.len(), 3);
    assert!(!claims.is_empty());
    assert_eq!(claims.iter().collect::<Vec<_>>(), [c, a, b]);
    assert_eq!(claims, Claims::new([a, b, c]));
    assert!(Claims::default().is_empty());
}

#[test]
fn invalid_signatures_are_rejected_before_proving() {
    let (key, message, signature) = signed(4, 7);
    let mut inputs = Aggregator::default();
    for length in [0, 1, signature.len() - 1] {
        assert_eq!(
            inputs.add_signature(&key, &message, &signature[..length]),
            Err(AggregateError::InvalidSignature)
        );
    }
    let mut extended = signature.to_vec();
    extended.push(0);
    assert_eq!(
        inputs.add_signature(&key, &message, &extended),
        Err(AggregateError::InvalidSignature)
    );
    for offset in [0, 16, 4240, signature.len() - 1] {
        let mut changed = signature;
        changed[offset] ^= 1;
        assert_eq!(
            inputs.add_signature(&key, &message, changed.as_slice()),
            Err(AggregateError::InvalidSignature)
        );
    }
    assert_eq!(
        inputs.add_signature(&B256::ZERO, &message, signature.as_slice()),
        Err(AggregateError::InvalidSignature)
    );
    assert_eq!(
        inputs.add_signature(&key, &B256::ZERO, signature.as_slice()),
        Err(AggregateError::InvalidSignature)
    );
    assert_eq!(
        inputs.prove(None, MAX_LOG_INV_RATE + 1).unwrap_err(),
        AggregateError::InvalidInput("log_inv_rate out of range")
    );
}

#[test]
fn reference_proofs_round_trip_merge_and_prune() {
    setup(4);
    let signatures = [signed(11, 1), signed(11, 2), signed(12, 3)];
    let expected = Claims::new(
        signatures[..2]
            .iter()
            .map(|(key, message, _)| (*key, *message)),
    );
    let mut leaf = Aggregator::with_capacity(2);
    let mut raw = Vec::new();
    for (key, message, signature) in &signatures[..2] {
        leaf.add_signature(key, message, signature.as_slice())
            .unwrap();
        let key = lean_vm::lean_sphincs::LeanSphincsPublicKey::from_bytes(&key.0);
        let signature = lean_vm::lean_sphincs::LeanSphincsSignature::from_bytes(&signature.0);
        assert!(lean_vm::lean_sphincs::verify(&key, &message.0, &signature));
        raw.push((key, message.0, signature));
    }
    let (key, message, signature) = &signatures[0];
    let mut rejected = *signature;
    rejected[0] ^= 1;
    assert_eq!(
        leaf.add_signature(key, message, rejected.as_slice()),
        Err(AggregateError::InvalidSignature)
    );
    let (reference_claims, reference_proof) =
        lean_vm::aggregate(&[], vec![], raw, None, OutputClaims::All, 1).unwrap();
    let leaf = leaf.prove(None, 1).unwrap();
    assert_eq!(leaf.claims(), &expected);
    assert!(leaf.verify(&expected));
    assert_eq!(reference_claims, self::reference_claims(&expected));
    assert_eq!(leaf.to_bytes(), reference_proof.to_bytes());

    let bytes = leaf.to_bytes();
    let native = AggregateProof::from_bytes(&bytes).unwrap();
    assert!(native.verify(&reference_claims));
    let imported = Aggregate::from_bytes(expected.clone(), &reference_proof.to_bytes()).unwrap();
    assert_eq!(imported.to_bytes(), bytes);
    assert!(imported.verify(&expected));

    let fewer = Claims::new([expected.iter().next().unwrap()]);
    let wrong_key = Claims::new([
        (B256::ZERO, signatures[0].1),
        (signatures[1].0, signatures[1].1),
    ]);
    let wrong_message = Claims::new([
        (signatures[0].0, B256::ZERO),
        (signatures[1].0, signatures[1].1),
    ]);
    for wrong in [Claims::default(), fewer, wrong_key, wrong_message] {
        assert!(!leaf.verify(&wrong));
        assert_eq!(
            Aggregate::from_bytes(wrong, &bytes).unwrap_err(),
            AggregateError::InvalidChild
        );
    }
    for length in [0, 1, 8, bytes.len() / 2, bytes.len() - 1] {
        assert_eq!(
            Aggregate::from_bytes(expected.clone(), &bytes[..length]).unwrap_err(),
            AggregateError::InvalidChild
        );
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert_eq!(
        Aggregate::from_bytes(expected.clone(), &trailing).unwrap_err(),
        AggregateError::InvalidChild
    );
    for offset in [0, 8, bytes.len() / 2, bytes.len() - 1] {
        let mut changed = bytes.clone();
        changed[offset] ^= 1;
        assert_eq!(
            Aggregate::from_bytes(expected.clone(), &changed).unwrap_err(),
            AggregateError::InvalidChild
        );
    }

    let retained = Claims::new(
        signatures[1..]
            .iter()
            .map(|(key, message, _)| (*key, *message)),
    );
    let mut parent = Aggregator::default();
    parent.add_child(imported).unwrap();
    // The same child claim arriving twice must not create a second obligation.
    parent.add_child(leaf.clone()).unwrap();
    let (key, message, signature) = &signatures[2];
    parent
        .add_signature(key, message, signature.as_slice())
        .unwrap();
    let parent = parent.prove(Some(&retained), 1).unwrap();
    assert_eq!(parent.claims(), &retained);
    assert!(parent.verify(&retained));
    assert!(
        AggregateProof::from_bytes(&parent.to_bytes())
            .unwrap()
            .verify(&self::reference_claims(&retained))
    );

    // This pruning step has only a child proof: the original signatures are not inputs.
    let only_new = Claims::new([(*key, *message)]);
    let mut pruned = Aggregator::default();
    pruned.add_child(parent).unwrap();
    let pruned = pruned.prove(Some(&only_new), 1).unwrap();
    assert_eq!(pruned.claims(), &only_new);
    assert!(pruned.verify(&only_new));
    assert!(!pruned.verify(&retained));

    let uncovered = Claims::new([(B256::ZERO, B256::ZERO)]);
    let mut missing = Aggregator::default();
    missing.add_child(pruned).unwrap();
    assert!(matches!(
        missing.prove(Some(&uncovered), 1),
        Err(AggregateError::InvalidInput(_))
    ));
    assert_eq!(
        Aggregator::default().prove(None, 1).unwrap_err(),
        AggregateError::InvalidInput("nothing to publish")
    );
    let mut bounded = Aggregator::default();
    for _ in 0..MAX_RECURSIONS {
        bounded.add_child(leaf.clone()).unwrap();
    }
    assert_eq!(
        bounded.add_child(leaf),
        Err(AggregateError::InvalidInput(
            "more than MAX_RECURSIONS children"
        ))
    );
}
