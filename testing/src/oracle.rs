use alloy_primitives::{B256, hex};
use serde::Serialize;
use std::fmt;

#[derive(Clone, Debug, Serialize)]
pub struct Failure {
    pub stage: String,
    pub detail: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub wire_hex: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ours_hex: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reference_hex: Option<String>,
}

impl Failure {
    pub fn new(stage: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            stage: stage.into(),
            detail: detail.into(),
            wire_hex: None,
            ours_hex: None,
            reference_hex: None,
        }
    }

    pub fn bytes(stage: &str, ours: &[u8], reference: &[u8]) -> Self {
        let first = ours.iter().zip(reference).position(|(a, b)| a != b);
        let mut failure = Self::new(
            stage,
            format!(
                "first differing byte: {first:?}; lengths {} and {}",
                ours.len(),
                reference.len()
            ),
        );
        failure.ours_hex = Some(hex::encode(ours));
        failure.reference_hex = Some(hex::encode(reference));
        failure
    }
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.stage, self.detail)
    }
}
impl std::error::Error for Failure {}

pub fn reference_verify(key: &B256, message: &B256, signature: &[u8]) -> bool {
    let Ok(bytes) = signature.try_into() else {
        return false;
    };
    reference_sphincs::verify(
        &reference_sphincs::LeanSphincsPublicKey::from_bytes(&key.0),
        &message.0,
        &reference_sphincs::LeanSphincsSignature::from_bytes(bytes),
    )
}

pub fn check_verification(
    key: &B256,
    message: &B256,
    signature: &[u8],
    expected: Option<bool>,
    stage: &str,
) -> Result<bool, Failure> {
    let ours = lean_sphincs::verify(key, message, signature);
    let reference = reference_verify(key, message, signature);
    if ours != reference || expected.is_some_and(|value| value != ours) {
        let mut error = Failure::new(
            stage,
            format!("ours={ours}, reference={reference}, expected={expected:?}"),
        );
        let mut wire = Vec::with_capacity(64 + signature.len());
        wire.extend_from_slice(&key.0);
        wire.extend_from_slice(&message.0);
        wire.extend_from_slice(signature);
        error.wire_hex = Some(hex::encode(wire));
        return Err(error);
    }
    Ok(ours)
}
