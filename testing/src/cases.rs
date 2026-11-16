use crate::{Failure, check_verification};
use alloy_primitives::B256;
use rand_chacha::{
    ChaCha20Rng,
    rand_core::{RngCore, SeedableRng},
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Case {
    pub secret_seed: [u8; 32],
    pub message: [u8; 32],
}

#[derive(Clone, Copy, Debug, Default, Serialize)]
pub struct CaseStats {
    pub key_comparisons: u64,
    pub signature_comparisons: u64,
    pub verification_checks: u64,
    pub negative_cases: u64,
}

/// Each case has its own ChaCha20 stream, independent of thread count or sharding.
pub fn generated_case(master_seed: [u8; 32], index: u64) -> Case {
    let mut rng = ChaCha20Rng::from_seed(master_seed);
    rng.set_stream(index);
    let mut case = Case {
        secret_seed: [0; 32],
        message: [0; 32],
    };
    rng.fill_bytes(&mut case.secret_seed);
    rng.fill_bytes(&mut case.message);
    case
}

pub fn check_case(case: &Case, index: u64) -> Result<CaseStats, Failure> {
    let seed = B256::new(case.secret_seed);
    let message = B256::new(case.message);
    let key = lean_sphincs::key_gen(&seed);
    let reference_key = reference_sphincs::key_gen(&case.secret_seed).to_bytes();
    if key.0 != reference_key {
        return Err(Failure::bytes("key generation", &key.0, &reference_key));
    }
    let signature =
        lean_sphincs::sign(&seed, &message).map_err(|e| Failure::new("signing", e.to_string()))?;
    let reference_signature = reference_sphincs::sign(&case.secret_seed, &case.message).to_bytes();
    if signature.as_slice() != reference_signature {
        return Err(Failure::bytes(
            "deterministic signature",
            signature.as_slice(),
            &reference_signature,
        ));
    }
    let mut stats = CaseStats {
        key_comparisons: 1,
        signature_comparisons: 1,
        ..CaseStats::default()
    };
    for bytes in [signature.as_slice(), reference_signature.as_slice()] {
        check_verification(&key, &message, bytes, Some(true), "cross verification")?;
        stats.verification_checks += 2;
    }
    // Repeat a sample of complete signing operations; an RNG was never supplied.
    if index.is_multiple_of(64) {
        let repeated = lean_sphincs::sign(&seed, &message)
            .map_err(|e| Failure::new("repeat signing", e.to_string()))?;
        let repeated_reference =
            reference_sphincs::sign(&case.secret_seed, &case.message).to_bytes();
        if repeated != signature {
            return Err(Failure::bytes(
                "repeat signing",
                repeated.as_slice(),
                signature.as_slice(),
            ));
        }
        if repeated_reference != reference_signature {
            return Err(Failure::bytes(
                "repeat reference signing",
                &repeated_reference,
                &reference_signature,
            ));
        }
        stats.signature_comparisons += 2;
    }
    // Every major field is tested on every generated valid signature.
    let n = index as usize;
    let bit = 1u8 << (index % 8);
    let fors_tree = n % 24;
    let offsets = [
        n % 16,
        16 + fors_tree * 176 + n % 16,
        16 + fors_tree * 176 + 16 + (n % 10) * 16 + n % 16,
        4240 + n % 4,
        4244 + n % 1024,
        5268 + n % 128,
        5396 + n % 4,
        5400 + n % 1024,
        6424 + n % 128,
        6552 + n % 4,
        6556 + n % 1024,
        7580 + n % 160,
    ];
    let mut mutated = signature;
    for offset in offsets {
        mutated[offset] ^= bit;
        check_verification(
            &key,
            &message,
            mutated.as_slice(),
            Some(false),
            &format!("signature mutation at {offset}"),
        )?;
        mutated[offset] ^= bit;
        stats.negative_cases += 1;
        stats.verification_checks += 2;
    }
    let mut wrong_key = key;
    wrong_key[n % 32] ^= bit;
    check_verification(
        &wrong_key,
        &message,
        signature.as_slice(),
        Some(false),
        "wrong key",
    )?;
    let mut wrong_message = message;
    wrong_message[n % 32] ^= bit;
    check_verification(
        &key,
        &wrong_message,
        signature.as_slice(),
        Some(false),
        "wrong message",
    )?;
    stats.negative_cases += 2;
    stats.verification_checks += 4;
    let mut swapped = key;
    swapped.0.rotate_left(16);
    if swapped != key {
        check_verification(
            &swapped,
            &message,
            signature.as_slice(),
            Some(false),
            "swapped public-key halves",
        )?;
        stats.negative_cases += 1;
        stats.verification_checks += 2;
    }
    for length in [0, 15, 16, 4239, 4240, 5395, 5396, 6551, 6552, 7739] {
        check_verification(
            &key,
            &message,
            &signature[..length],
            Some(false),
            "truncated signature",
        )?;
        stats.negative_cases += 1;
        stats.verification_checks += 2;
    }
    let mut extended = signature.to_vec();
    extended.extend_from_slice(&[0, 0xff, 1]);
    check_verification(&key, &message, &extended, Some(false), "extended signature")?;
    stats.negative_cases += 1;
    stats.verification_checks += 2;
    Ok(stats)
}
