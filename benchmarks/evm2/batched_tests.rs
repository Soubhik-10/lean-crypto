mod batched;
mod reference;

use alloy_primitives::B256;

fn check(seed: B256, message: B256) {
    let key = lean_sphincs::key_gen(&seed);
    assert_eq!(batched::key_gen(&seed), key);
    assert_eq!(reference::key_gen(&seed), key);
    let signature = lean_sphincs::sign(&seed, &message).unwrap();
    assert_eq!(batched::sign(&seed, &message), signature);
    assert_eq!(reference::sign(&seed, &message), signature);
    assert!(batched::verify(&key, &message, &signature[..]));
    for at in [0, 16, 32, 190, 4239, 4240, 5000, 7739] {
        let mut invalid = signature;
        invalid[at] ^= 0x80;
        assert_eq!(
            batched::verify(&key, &message, &invalid[..]),
            reference::verify(&key, &message, &invalid[..])
        );
    }
    assert!(!batched::verify(&key, &message, &signature[..7739]));
    let mut extended = signature.to_vec();
    extended.push(0);
    assert!(!batched::verify(&key, &message, &extended));
    assert!(!batched::verify(&key, &message, &[]));
    let mut wrong_key = key;
    wrong_key[0] ^= 1;
    assert!(!batched::verify(&wrong_key, &message, &signature[..]));
    let mut wrong_message = message;
    wrong_message[0] ^= 1;
    assert!(!batched::verify(&key, &wrong_message, &signature[..]));
}

#[test]
fn specification_signatures_are_unchanged() {
    let vectors: serde_json::Value = serde_json::from_str(include_str!(
        "../../crates/lean-sphincs/tests/vectors/sign.json"
    ))
    .unwrap();
    for case in vectors.as_array().unwrap() {
        if let Some(expected) = case["expected"].as_str() {
            let seed = case["seed"].as_str().unwrap().parse().unwrap();
            let message = case["message"].as_str().unwrap().parse().unwrap();
            assert_eq!(
                batched::sign(&seed, &message),
                expected.parse::<lean_sphincs::Signature>().unwrap()
            );
            check(seed, message);
        }
    }
}

#[test]
fn randomized_keys_signatures_and_rejections_match_both_implementations() {
    for index in 0..32u64 {
        let mut input = [0; 9];
        input[..8].copy_from_slice(&index.to_be_bytes());
        let seed = B256::new(reference_keccak::hash(&input));
        input[8] = 1;
        let message = B256::new(reference_keccak::hash(&input));
        check(seed, message);
    }
}
