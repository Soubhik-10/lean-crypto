//! An aggregate and its exact, independently supplied claims.

use crate::{AggregateError, Claims};
use lean_vm::AggregateProof;

/// An aggregate bound to its exact leanSPHINCS claims.
///
/// Public constructors either generate a proof or fully verify received proof
/// bytes. Fields are private so a checked proof cannot be relabelled. Cloning
/// explicitly copies the proof; move it into [`crate::Aggregator::add_child`]
/// when the original is no longer needed.
#[derive(Clone, Debug)]
pub struct Aggregate {
    pub(crate) claims: Claims,
    pub(crate) proof: AggregateProof,
}

impl Aggregate {
    /// Decodes and fully verifies reference proof bytes against expected claims.
    ///
    /// The proof does not carry its claims. The caller must reconstruct them
    /// independently and bound `bytes.len()` before calling this function.
    /// Returns [`AggregateError::InvalidChild`] for malformed bytes or a proof
    /// that does not establish exactly `claims`, including its deferred check.
    pub fn from_bytes(claims: Claims, bytes: &[u8]) -> Result<Self, AggregateError> {
        let proof = AggregateProof::from_bytes(bytes).ok_or(AggregateError::InvalidChild)?;
        if !proof.verify(&claims.inner) {
            return Err(AggregateError::InvalidChild);
        }
        Ok(Self { claims, proof })
    }

    /// Returns the exact claims established by this aggregate.
    pub fn claims(&self) -> &Claims {
        &self.claims
    }

    /// Serializes the unchanged reference proof, without the claims.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.proof.to_bytes()
    }

    /// Fully verifies the proof against exactly `expected`, without allocating
    /// or converting another claim list in this adapter.
    pub fn verify(&self, expected: &Claims) -> bool {
        self.proof.verify(&expected.inner)
    }
}
