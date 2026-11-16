use alloy_primitives::{B256, keccak256};
use lean_sphincs::{Signature, key_gen, sign, verify};
use secp256k1::{Message, SecretKey, ecdsa::RecoverableSignature};
use serde::Deserialize;

use crate::reference;

#[derive(Deserialize)]
struct Vector {
    name: String,
    seed: String,
    message: String,
    expected: Option<String>,
}

pub struct Input {
    pub name: String,
    pub seed: B256,
    pub message: B256,
    pub key: B256,
    pub signature: Signature,
    pub parsed_key: reference::PublicKey,
    pub parsed_signature: reference::ParsedSignature,
}

pub struct Fixtures {
    pub inputs: Vec<Input>,
    pub late: Signature,
    pub counter: Signature,
    pub fors: Signature,
    pub wrong_key: B256,
    pub wrong_message: B256,
    pub overlong: Vec<u8>,
    pub ec_message: B256,
    pub ec_signature: [u8; 64],
    pub ec_id: u8,
    pub ec_public_key: [u8; 65],
    pub ec_word: [u8; 32],
}

impl Fixtures {
    pub fn new(extra_cases: usize) -> Self {
        let vectors: Vec<Vector> =
            serde_json::from_str(include_str!("../../../tests/vectors/sign.json")).unwrap();
        let mut inputs = Vec::new();
        for vector in vectors.into_iter().filter(|v| v.expected.is_some()) {
            let message = vector.message.parse().unwrap();
            inputs.push(Self::input(
                vector.name,
                vector.seed.parse().unwrap(),
                message,
                vector.expected,
            ));
        }
        assert_eq!(
            inputs.len(),
            3,
            "all positive reference vectors must be present"
        );
        for index in 0..extra_cases {
            let seed = keccak256(format!("lean-sphincs benchmark seed {index}").as_bytes());
            let message = keccak256(format!("lean-sphincs benchmark message {index}").as_bytes());
            inputs.push(Self::input(
                format!("corpus_{index:02}"),
                seed,
                message,
                None,
            ));
        }
        let first = &inputs[0];
        let mut late = first.signature;
        *late.last_mut().unwrap() ^= 1;
        let mut counter = first.signature;
        counter[16 + 24 * 11 * 16] ^= 1;
        let mut fors = first.signature;
        fors[16] ^= 1;
        let mut wrong_key = first.key;
        wrong_key[0] ^= 1;
        let mut wrong_message = first.message;
        wrong_message[0] ^= 1;
        let mut overlong = first.signature.to_vec();
        overlong.push(0);
        for (key, message, signature) in [
            (&first.key, &first.message, late.as_slice()),
            (&first.key, &first.message, counter.as_slice()),
            (&first.key, &first.message, fors.as_slice()),
            (&wrong_key, &first.message, first.signature.as_slice()),
            (&first.key, &wrong_message, first.signature.as_slice()),
            (&first.key, &first.message, &overlong),
            (&first.key, &first.message, &first.signature[..7739]),
            (&first.key, &first.message, &[]),
        ] {
            assert!(!verify(key, message, signature));
            assert!(!reference::verify(key, message, signature));
        }
        let ec_message = B256::repeat_byte(42);
        let secret = SecretKey::from_secret_bytes([1; 32]).unwrap();
        let signed = RecoverableSignature::sign_ecdsa_recoverable(
            Message::from_digest(ec_message.0),
            &secret,
        );
        let (id, ec_signature) = signed.serialize_compact();
        let expected = signed
            .recover_ecdsa(Message::from_digest(ec_message.0))
            .unwrap();
        let mut word = keccak256(&expected.serialize_uncompressed()[1..]);
        word[..12].fill(0);
        assert_eq!(
            evm2::precompiles::crypto()
                .secp256k1_ecrecover(&ec_signature, id.to_u8(), &ec_message.0)
                .unwrap(),
            word.0
        );
        Self {
            inputs,
            late,
            counter,
            fors,
            wrong_key,
            wrong_message,
            overlong,
            ec_message,
            ec_signature,
            ec_id: id.to_u8(),
            ec_public_key: expected.serialize_uncompressed(),
            ec_word: word.0,
        }
    }

    fn input(name: String, seed: B256, message: B256, expected: Option<String>) -> Input {
        let key = key_gen(&seed);
        let signature = sign(&seed, &message).unwrap();
        if let Some(expected) = expected {
            assert_eq!(signature, expected.parse::<Signature>().unwrap(), "{name}");
        }
        assert_eq!(reference::key_gen(&seed), key, "{name}");
        assert_eq!(reference::sign(&seed, &message), signature, "{name}");
        assert!(verify(&key, &message, signature.as_slice()), "{name}");
        assert!(
            reference::verify(&key, &message, signature.as_slice()),
            "{name}"
        );
        Input {
            name,
            seed,
            message,
            key,
            signature,
            parsed_key: reference::PublicKey::from_bytes(&key.0),
            parsed_signature: reference::ParsedSignature::from_bytes(&signature.0),
        }
    }
}
