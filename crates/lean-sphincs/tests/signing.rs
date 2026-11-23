//! Pinned signing/key-generation vectors and deterministic round trips.

use alloy_primitives::{B256, b256, hex};
use lean_sphincs::{SignError, key_gen, sign, verify};
use serde::Deserialize;

#[derive(Deserialize)]
struct KeyVector {
    name: String,
    seed: String,
    expected: Option<String>,
}

#[derive(Deserialize)]
struct SignVector {
    name: String,
    seed: String,
    message: String,
    expected: Option<String>,
}

#[test]
fn key_generation_matches_pinned_vectors() {
    let cases: Vec<KeyVector> = serde_json::from_str(include_str!("vectors/key_gen.json")).unwrap();
    assert_eq!(cases.len(), 4);
    for case in cases {
        match case.seed.parse::<B256>() {
            Ok(seed) => {
                let expected: B256 = case.expected.expect("valid typed seed").parse().unwrap();
                assert_eq!(key_gen(&seed), expected, "{}", case.name);
            }
            Err(_) => assert_eq!(case.expected, None, "{}", case.name),
        }
    }
}

#[test]
fn signing_matches_every_pinned_byte() {
    let cases: Vec<SignVector> = serde_json::from_str(include_str!("vectors/sign.json")).unwrap();
    assert_eq!(cases.len(), 5);
    for case in cases {
        if let (Ok(seed), Ok(message)) = (case.seed.parse::<B256>(), case.message.parse::<B256>()) {
            let expected = hex::decode(case.expected.expect("valid typed inputs")).unwrap();
            let signature = sign(&seed, &message).unwrap();
            assert_eq!(signature.len(), expected.len());
            let difference = signature
                .iter()
                .zip(&expected)
                .position(|(actual, expected)| actual != expected);
            assert_eq!(
                difference, None,
                "{}: first mismatched signature byte",
                case.name
            );
            assert!(
                verify(&key_gen(&seed), &message, signature.as_slice()),
                "{}",
                case.name
            );
        } else {
            assert_eq!(case.expected, None, "{}", case.name);
        }
    }
}

#[test]
fn signing_is_deterministic_and_binds_seed_and_message() {
    let seed = b256!("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186");
    let message = B256::repeat_byte(42);
    let signature = sign(&seed, &message).unwrap();
    assert_eq!(sign(&seed, &message).unwrap(), signature);
    let public_key = key_gen(&seed);
    assert!(verify(&public_key, &message, signature.as_slice()));
    let mut other_message = message;
    other_message[0] ^= 1;
    assert!(!verify(&public_key, &other_message, signature.as_slice()));
    let mut other_seed = seed;
    other_seed[31] ^= 1;
    let other_key = key_gen(&other_seed);
    assert_ne!(other_key, public_key);
    assert!(!verify(&other_key, &message, signature.as_slice()));
}

#[test]
fn counter_error_identifies_the_layer() {
    assert_eq!(
        SignError::CounterExhausted { layer: 2 }.to_string(),
        "no admissible WOTS+C counter for layer 2"
    );
}
