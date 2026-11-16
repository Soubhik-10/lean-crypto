use alloy_primitives::hex;
use lean_sphincs_testing::{check_mutated_fixture, check_wire, fixtures, generated_case};

#[test]
fn chacha_stream_zero_matches_known_answer() {
    let case = generated_case([0; 32], 0);
    assert_eq!(
        hex::encode(case.secret_seed),
        "76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7"
    );
    assert_eq!(
        hex::encode(case.message),
        "da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586"
    );
}

#[test]
fn generator_is_random_access_and_replayable() {
    let seed = [42; 32];
    let first = generated_case(seed, 12345);
    let _other = generated_case(seed, 4);
    let replayed = generated_case(seed, 12345);
    assert_eq!(first.secret_seed, replayed.secret_seed);
    assert_eq!(first.message, replayed.message);
    assert_ne!(first.secret_seed, generated_case(seed, 12346).secret_seed);
}

#[test]
fn every_valid_fixture_reaches_both_verifiers() {
    for (index, case) in fixtures().iter().enumerate() {
        let mut wire = case.key.to_vec();
        wire.extend_from_slice(&case.message.0);
        wire.extend_from_slice(&case.signature);
        assert!(check_wire(&wire).unwrap());
        assert!(check_mutated_fixture(&[index as u8]).unwrap());
        for length in [0, 1, 31, 32, 63, 64, 65, wire.len() - 1] {
            assert!(!check_wire(&wire[..length]).unwrap());
        }
        wire.push(0);
        assert!(!check_wire(&wire).unwrap());
    }
}

#[test]
fn structured_edits_reach_each_signature_region() {
    for selector in 0..3 {
        for position in [
            0u16, 15, 16, 4239, 4240, 4244, 5268, 5396, 5400, 6424, 6552, 6556, 7580, 7739,
        ] {
            let [low, high] = position.to_le_bytes();
            assert!(!check_mutated_fixture(&[selector, 0, low, high, 1]).unwrap());
        }
    }
}
