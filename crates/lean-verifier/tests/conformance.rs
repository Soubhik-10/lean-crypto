//! Full aggregate verdicts and canonical decoding against the pinned reference.

use lean_verifier::{AggregateClaims, AggregateProof, B256, Verifier, VerifyError};
use lean_vm::{AggregateClaims as ReferenceClaims, AggregateProof as ReferenceProof, OutputClaims};
use std::sync::OnceLock;

fn verifier() -> &'static Verifier {
    static VERIFIER: OnceLock<Verifier> = OnceLock::new();
    VERIFIER.get_or_init(|| {
        Verifier::new(reference_aggregation::unified_guest().stacked_bytecode()).unwrap()
    })
}

fn setup() {
    static SETUP: std::sync::Once = std::sync::Once::new();
    SETUP.call_once(|| lean_vm::setup(4));
}

fn signature(
    seed: u8,
    message: u8,
) -> (
    lean_vm::lean_sphincs::LeanSphincsPublicKey,
    [u8; 32],
    lean_vm::lean_sphincs::LeanSphincsSignature,
) {
    let seed = B256::repeat_byte(seed);
    let message = B256::repeat_byte(message);
    let key = lean_sphincs::key_gen(&seed);
    let signature = lean_sphincs::sign(&seed, &message).unwrap();
    (
        lean_vm::lean_sphincs::LeanSphincsPublicKey::from_bytes(&key.0),
        message.0,
        lean_vm::lean_sphincs::LeanSphincsSignature::from_bytes(&signature.0),
    )
}

fn claims(reference: &ReferenceClaims) -> AggregateClaims {
    AggregateClaims {
        lean_xmss: reference
            .lean_xmss
            .iter()
            .map(|(key, message)| (B256::new(key.to_bytes()), B256::new(*message)))
            .collect(),
        lean_sphincs: reference
            .lean_sphincs
            .iter()
            .map(|(key, message)| (B256::new(key.to_bytes()), B256::new(*message)))
            .collect(),
        da_commitment: reference.da_commitment.map(B256::new),
    }
}

fn reference_claims(claims: &AggregateClaims) -> ReferenceClaims {
    ReferenceClaims {
        lean_xmss: claims
            .lean_xmss
            .iter()
            .map(|(key, message)| {
                (
                    lean_vm::lean_xmss::LeanXmssPublicKey::from_bytes(&key.0),
                    message.0,
                )
            })
            .collect(),
        lean_sphincs: claims
            .lean_sphincs
            .iter()
            .map(|(key, message)| {
                (
                    lean_vm::lean_sphincs::LeanSphincsPublicKey::from_bytes(&key.0),
                    message.0,
                )
            })
            .collect(),
        da_commitment: claims.da_commitment.map(|root| root.0),
    }
}

fn compare(expected: &AggregateClaims, bytes: &[u8]) -> bool {
    let ours = AggregateProof::from_bytes(bytes);
    let theirs = ReferenceProof::from_bytes(bytes);
    assert_eq!(
        ours.is_ok(),
        theirs.is_some(),
        "decoder disagreement, {} bytes",
        bytes.len()
    );
    if let Ok(proof) = &ours {
        assert_eq!(proof.to_bytes(), bytes, "accepted encoding is canonical");
    }
    let reference = theirs.is_some_and(|proof| proof.verify(&reference_claims(expected)));
    let actual = ours.is_ok_and(|proof| verifier().verify(expected, &proof).is_ok());
    assert_eq!(
        actual,
        reference,
        "verifier disagreement, {} bytes",
        bytes.len()
    );
    actual
}

fn aggregate(
    raw: Vec<(
        lean_vm::lean_sphincs::LeanSphincsPublicKey,
        [u8; 32],
        lean_vm::lean_sphincs::LeanSphincsSignature,
    )>,
    rate: usize,
) -> (ReferenceClaims, ReferenceProof) {
    setup();
    lean_vm::aggregate(&[], vec![], raw, None, OutputClaims::All, rate).unwrap()
}

#[test]
fn valid_proofs_at_each_supported_rate() {
    for rate in 1..=4 {
        let (expected, proof) = aggregate(vec![signature(21, rate as u8)], rate);
        let expected = claims(&expected);
        let bytes = proof.to_bytes();
        assert!(compare(&expected, &bytes), "rate {rate}");
    }
}

#[test]
fn recursive_merge_and_pruning_without_original_signatures() {
    let left = aggregate(vec![signature(31, 1), signature(31, 2)], 1);
    let right = aggregate(vec![signature(31, 2), signature(32, 3)], 1);
    let expected = ReferenceClaims {
        lean_sphincs: vec![
            left.0.lean_sphincs[1],
            *right
                .0
                .lean_sphincs
                .iter()
                .find(|(_, message)| *message == [3; 32])
                .unwrap(),
        ],
        ..Default::default()
    };
    let mut expected = expected;
    expected.lean_sphincs.sort_unstable();
    expected.lean_sphincs.dedup();
    let (root_claims, root) = lean_vm::aggregate(
        &[left, right],
        vec![],
        vec![],
        None,
        OutputClaims::Only(&expected),
        1,
    )
    .unwrap();
    assert_eq!(root_claims, expected);
    let bytes = root.to_bytes();
    assert!(
        bytes[8..8 + lean_verifier::BYTECODE_VARIABLES * 16]
            .iter()
            .any(|byte| *byte != 0)
    );
    assert!(compare(&claims(&expected), &bytes));

    // The point is not merely decoded: changing it must fail the complete deferred check.
    let mut wrong_point = bytes;
    wrong_point[8] ^= 1;
    assert!(!compare(&claims(&expected), &wrong_point));
    let only = ReferenceClaims {
        lean_sphincs: vec![expected.lean_sphincs[0]],
        ..Default::default()
    };
    let (pruned_claims, pruned) = lean_vm::aggregate(
        &[(root_claims, root)],
        vec![],
        vec![],
        None,
        OutputClaims::Only(&only),
        1,
    )
    .unwrap();
    assert_eq!(pruned_claims, only);
    assert!(compare(&claims(&only), &pruned.to_bytes()));
    assert!(!compare(&claims(&expected), &pruned.to_bytes()));
}

#[test]
fn both_signature_schemes_and_da_bind_the_complete_statement() {
    setup();
    let (secret, key) = lean_vm::lean_xmss::key_gen(&[41; 32]);
    secret.prepare(7);
    let message = [42; 32];
    let sig = lean_vm::lean_xmss::sign(&secret, &message, 7);
    let blob: lean_vm::lean_da::Blob = core::array::from_fn(|i| (i as u128).wrapping_mul(13));
    let matrix = lean_vm::lean_da::BlobMatrix::build(&[blob]).unwrap();
    let (expected, proof) = lean_vm::aggregate(
        &[],
        vec![(key, message, sig)],
        vec![signature(43, 44)],
        Some(&matrix),
        OutputClaims::All,
        1,
    )
    .unwrap();
    let expected = claims(&expected);
    let bytes = proof.to_bytes();
    assert!(compare(&expected, &bytes));
    let mut wrong = expected.clone();
    wrong.da_commitment = None;
    assert!(!compare(&wrong, &bytes));
    wrong.da_commitment = Some(B256::ZERO);
    assert!(!compare(&wrong, &bytes));
    wrong = expected.clone();
    wrong.lean_xmss[0].1[0] ^= 1;
    assert!(!compare(&wrong, &bytes));
    wrong = expected.clone();
    wrong.lean_sphincs[0].0[16] ^= 1;
    assert!(!compare(&wrong, &bytes));
    wrong = expected;
    core::mem::swap(&mut wrong.lean_xmss, &mut wrong.lean_sphincs);
    assert!(!compare(&wrong, &bytes));
}

#[test]
fn malformed_proofs_and_wrong_claims_match_reference_rejection() {
    let (expected, proof) = aggregate(vec![signature(51, 1), signature(51, 2)], 1);
    let expected = claims(&expected);
    let bytes = proof.to_bytes();
    assert!(compare(&expected, &bytes));
    for length in [0, 1, 7, 8, 15, 375, 376, bytes.len() / 2, bytes.len() - 1] {
        assert!(!compare(&expected, &bytes[..length]));
    }
    for length in (0..bytes.len()).step_by((bytes.len() / 19).max(1)) {
        assert!(!compare(&expected, &bytes[..length]));
    }
    let mut trailing = bytes.clone();
    trailing.extend([0; 16]);
    assert!(!compare(&expected, &trailing));
    for count in [0, 1, 22, 24, u32::MAX as u64, u64::MAX] {
        let mut changed = bytes.clone();
        changed[..8].copy_from_slice(&count.to_le_bytes());
        assert!(!compare(&expected, &changed));
    }
    let stream = 8 + lean_verifier::BYTECODE_VARIABLES * 16;
    for count in [0, u32::MAX] {
        let mut changed = bytes.clone();
        changed[stream..stream + 4].copy_from_slice(&count.to_le_bytes());
        assert!(!compare(&expected, &changed));
    }
    // Announced memory/table sizes and rate are untrusted field elements.
    for index in 0..8 {
        for (low, high) in [(0u64, 0u64), (u64::MAX, 0), (1, u64::MAX)] {
            let mut changed = bytes.clone();
            let start = stream + 4 + index * 16;
            changed[start..start + 8].copy_from_slice(&low.to_le_bytes());
            changed[start + 8..start + 16].copy_from_slice(&high.to_le_bytes());
            assert!(!compare(&expected, &changed));
        }
    }
    // Exercise the wire decoder's independent Merkle size/shape bounds.
    let scalar_count = u32::from_le_bytes(bytes[stream..stream + 4].try_into().unwrap()) as usize;
    let phases = stream + 4 + scalar_count * 16;
    let queries = phases + 4;
    let query_count = u32::from_le_bytes(bytes[queries..queries + 4].try_into().unwrap()) as usize;
    let dimensions = queries + 4 + query_count * 4;
    for field in [
        phases,
        queries,
        queries + 4,
        dimensions,
        dimensions + 4,
        dimensions + 8,
    ] {
        for value in [0u32, u32::MAX] {
            let mut changed = bytes.clone();
            changed[field..field + 4].copy_from_slice(&value.to_le_bytes());
            assert!(!compare(&expected, &changed));
        }
    }
    let mut state = 0x72a0_986b_634e_d125u64;
    for _ in 0..64 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let mut changed = bytes.clone();
        let offset = state as usize % changed.len();
        changed[offset] ^= 1 << ((state >> 32) % 8);
        assert!(!compare(&expected, &changed), "mutated byte {offset}");
    }
    let mut wrong = expected.clone();
    wrong.lean_sphincs.reverse();
    let decoded = AggregateProof::from_bytes(&bytes).unwrap();
    assert_eq!(
        verifier().verify(&wrong, &decoded),
        Err(VerifyError::Claims)
    );
    assert!(!compare(&wrong, &bytes));
    wrong = expected.clone();
    wrong.lean_sphincs.push(wrong.lean_sphincs[1]);
    assert!(!compare(&wrong, &bytes));
    wrong = expected.clone();
    wrong.lean_sphincs.pop();
    assert!(!compare(&wrong, &bytes));
    wrong = expected;
    wrong.lean_sphincs[0].1[0] ^= 1;
    assert!(!compare(&wrong, &bytes));
    assert!(!compare(&AggregateClaims::default(), &bytes));
}
