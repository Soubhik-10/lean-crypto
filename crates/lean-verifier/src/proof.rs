//! The pinned aggregate proof encoding, without a trusted verdict or claim list.

use crate::{BYTECODE_VARIABLES, VerifyError, vm};
use alloc::vec::Vec;

/// Decoded aggregate proof bytes. Decoding does not verify a proof.
///
/// Call [`crate::Verifier::verify`] with independently reconstructed expected
/// claims. The caller must bound untrusted byte lengths before decoding.
#[derive(Clone, Debug)]
pub struct AggregateProof {
    pub(crate) point: Vec<vm::E>,
    pub(crate) execution: vm::Proof,
}

impl AggregateProof {
    /// Decodes exactly one reference aggregate, rejecting malformed counts,
    /// truncation, noncanonical Merkle encodings and trailing bytes.
    /// No claim is accepted until [`crate::Verifier::verify`] succeeds.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, VerifyError> {
        let (count, rest) = bytes
            .split_first_chunk::<8>()
            .ok_or(VerifyError::Encoding)?;
        if u64::from_le_bytes(*count) != BYTECODE_VARIABLES as u64 {
            return Err(VerifyError::Encoding);
        }
        let (coordinates, proof) = rest
            .split_at_checked(BYTECODE_VARIABLES * 16)
            .ok_or(VerifyError::Encoding)?;
        let point = coordinates
            .chunks_exact(16)
            .map(|coordinate| {
                let mut low = [0u8; 8];
                let mut high = [0u8; 8];
                low.copy_from_slice(&coordinate[..8]);
                high.copy_from_slice(&coordinate[8..]);
                vm::E::new(u64::from_le_bytes(low), u64::from_le_bytes(high))
            })
            .collect();
        let execution = vm::Proof::from_bytes(proof).ok_or(VerifyError::Encoding)?;
        Ok(Self { point, execution })
    }

    /// Serializes in the reference's unchanged format, without claims.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = (BYTECODE_VARIABLES as u64).to_le_bytes().to_vec();
        for value in &self.point {
            bytes.extend(value.c0.to_le_bytes());
            bytes.extend(value.c1.to_le_bytes());
        }
        bytes.extend(self.execution.to_bytes());
        bytes
    }
}
