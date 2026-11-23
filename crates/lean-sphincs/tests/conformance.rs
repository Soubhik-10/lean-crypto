//! Pinned conformance, mutation and malformed-input tests.

mod common;

use alloy_primitives::{B256, hex};
use lean_sphincs::{SIGNATURE_BYTES, verify};

#[test]
fn pinned_ethlib_vectors() {
    let vectors = common::vectors();
    assert_eq!(vectors.len(), 26);
    for case in vectors {
        let public_key = hex::decode(&case.public_key).unwrap();
        let message = hex::decode(&case.message).unwrap();
        let signature = hex::decode(&case.signature).unwrap();
        if let (Ok(public_key), Ok(message)) = (
            B256::try_from(public_key.as_slice()),
            B256::try_from(message.as_slice()),
        ) {
            // EthLib uses null for malformed lengths; this API returns false.
            assert_eq!(
                verify(&public_key, &message, &signature),
                case.expected.unwrap_or(false),
                "{}",
                case.name
            );
        } else {
            assert_eq!(
                case.expected, None,
                "{} must reject malformed typed inputs",
                case.name
            );
        }
    }
}

#[test]
fn every_signature_byte_is_authenticated() {
    let (public_key, message, mut signature) = common::known_answer();
    assert!(verify(&public_key, &message, &signature));
    for offset in 0..signature.len() {
        signature[offset] ^= 1;
        assert!(
            !verify(&public_key, &message, &signature),
            "signature byte {offset}"
        );
        signature[offset] ^= 1;
    }
}

#[test]
fn every_key_and_message_byte_is_authenticated() {
    let (public_key, message, signature) = common::known_answer();
    for offset in 0..32 {
        let mut altered_key = public_key;
        altered_key[offset] ^= 1;
        assert!(
            !verify(&altered_key, &message, &signature),
            "public key byte {offset}"
        );
        let mut altered_message = message;
        altered_message[offset] ^= 1;
        assert!(
            !verify(&public_key, &altered_message, &signature),
            "message byte {offset}"
        );
    }
}

#[test]
fn rejects_every_truncation_and_trailing_bytes() {
    let (public_key, message, mut signature) = common::known_answer();
    for length in 0..SIGNATURE_BYTES {
        assert!(
            !verify(&public_key, &message, &signature[..length]),
            "length {length}"
        );
    }
    for _ in 0..32 {
        signature.push(0);
        assert!(!verify(&public_key, &message, &signature));
    }
}

#[test]
fn rejects_arbitrary_full_length_encodings_without_panicking() {
    let mut state = 0x748b_96c0_51d2_a3efu64;
    let mut signature = [0u8; SIGNATURE_BYTES];
    for _ in 0..512 {
        for byte in &mut signature {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *byte = state as u8;
        }
        let public_key = B256::repeat_byte(state as u8);
        let message = B256::repeat_byte((state >> 8) as u8);
        assert!(!verify(&public_key, &message, &signature));
    }
}
