//! Thin benchmark adapters; wire cases include parsing or serialization.

use alloy_primitives::B256;
pub use reference_sphincs::{
    LeanSphincsPublicKey as PublicKey, LeanSphincsSignature as ParsedSignature,
    verify as verify_parsed,
};

pub fn key_gen(seed: &B256) -> B256 {
    B256::new(reference_sphincs::key_gen(&seed.0).to_bytes())
}

pub fn sign(seed: &B256, message: &B256) -> lean_sphincs::Signature {
    lean_sphincs::Signature::new(reference_sphincs::sign(&seed.0, &message.0).to_bytes())
}

pub fn verify(key: &B256, message: &B256, signature: &[u8]) -> bool {
    let Ok(bytes) = signature.try_into() else {
        return false;
    };
    verify_parsed(
        &PublicKey::from_bytes(&key.0),
        &message.0,
        &ParsedSignature::from_bytes(bytes),
    )
}
