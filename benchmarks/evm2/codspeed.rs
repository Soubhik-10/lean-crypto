#[cfg(not(feature = "asm-keccak"))]
#[path = "codspeed_cases.rs"]
mod portable;

#[cfg(feature = "asm-keccak")]
#[path = "codspeed_cases.rs"]
mod assembly;

use alloy_primitives::B256;
use evm2::precompiles;
use lean_sphincs::{Signature, key_gen, sign, verify};
use secp256k1::{Message, SecretKey, ecdsa::RecoverableSignature};
use std::sync::OnceLock;

struct Case {
    seed: B256,
    message: B256,
    public_key: B256,
    signature: Signature,
}

struct Fixtures {
    cases: Vec<Case>,
    late_reject: Signature,
    ec_message: B256,
    ec_signature: [u8; 64],
    ec_recovery_id: u8,
}

fn fixtures() -> &'static Fixtures {
    static FIXTURES: OnceLock<Fixtures> = OnceLock::new();
    FIXTURES.get_or_init(|| {
        let vectors: serde_json::Value =
            serde_json::from_str(include_str!("../../tests/vectors/sign.json")).unwrap();
        let cases: Vec<_> = vectors
            .as_array()
            .unwrap()
            .iter()
            .filter(|case| case["expected"].is_string())
            .map(|case| {
                let seed = case["seed"].as_str().unwrap().parse().unwrap();
                let message = case["message"].as_str().unwrap().parse().unwrap();
                let public_key = key_gen(&seed);
                let signature = sign(&seed, &message).unwrap();
                let expected: Signature = case["expected"].as_str().unwrap().parse().unwrap();
                assert_eq!(signature, expected);
                assert!(verify(&public_key, &message, signature.as_slice()));
                Case {
                    seed,
                    message,
                    public_key,
                    signature,
                }
            })
            .collect();
        assert_eq!(cases.len(), 3);
        let mut late_reject = cases[0].signature;
        *late_reject.last_mut().unwrap() ^= 1;
        assert!(!verify(
            &cases[0].public_key,
            &cases[0].message,
            late_reject.as_slice()
        ));
        let ec_message = B256::repeat_byte(42);
        let secret = SecretKey::from_secret_bytes([1; 32]).unwrap();
        let signature = RecoverableSignature::sign_ecdsa_recoverable(
            Message::from_digest(ec_message.0),
            &secret,
        );
        let (ec_recovery_id, ec_signature) = signature.serialize_compact();
        assert!(
            precompiles::crypto()
                .secp256k1_ecrecover(&ec_signature, ec_recovery_id.to_u8(), &ec_message.0)
                .is_ok()
        );
        Fixtures {
            cases,
            late_reject,
            ec_message,
            ec_signature,
            ec_recovery_id: ec_recovery_id.to_u8(),
        }
    })
}

fn main() {
    // Fixture parsing, signing and correctness checks stay outside every measurement.
    let _ = fixtures();
    divan::main();
}
