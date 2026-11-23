//! Admission of checked inputs and reference proof generation.

use crate::{Aggregate, AggregateError, Claims, MAX_RECURSIONS};
use lean_sphincs::B256;
use lean_vm::{
    AggregateClaims, AggregateProof, OutputClaims,
    lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature},
};

const _: () = assert!(lean_sphincs::PUBLIC_KEY_BYTES == lean_vm::lean_sphincs::PUB_KEY_SIZE);
const _: () = assert!(lean_sphincs::MESSAGE_BYTES == lean_vm::lean_sphincs::MESSAGE_LEN);
const _: () = assert!(lean_sphincs::SIGNATURE_BYTES == lean_vm::lean_sphincs::SIG_SIZE);

/// Inputs for one reference aggregation node.
///
/// Each fresh signature is checked once on admission with `lean-sphincs`.
/// Received child proofs are checked by [`Aggregate::from_bytes`]. Adding a
/// child moves its claims and proof buffers rather than serializing or cloning
/// them. The reference guest still constrains every signature and child proof.
#[derive(Debug, Default)]
pub struct Aggregator {
    children: Vec<(AggregateClaims, AggregateProof)>,
    signatures: Vec<(LeanSphincsPublicKey, [u8; 32], LeanSphincsSignature)>,
}

impl Aggregator {
    /// Reserves space for a known number of fresh signatures.
    ///
    /// This avoids growing or overallocating the raw-input buffer when the
    /// caller already knows its batch size. The count must be bounded before
    /// using untrusted input. Children are still moved in as they arrive.
    pub fn with_capacity(signature_count: usize) -> Self {
        Self {
            children: Vec::new(),
            signatures: Vec::with_capacity(signature_count),
        }
    }

    /// Verifies and retains a fresh signature on the exact message digest.
    ///
    /// Returns [`AggregateError::InvalidSignature`] for invalid signature bytes,
    /// including the wrong length. Rejection leaves the aggregator unchanged.
    /// Callers must bound the total signature count before admission.
    pub fn add_signature(
        &mut self,
        public_key: &B256,
        message: &B256,
        signature: &[u8],
    ) -> Result<(), AggregateError> {
        let bytes = signature
            .try_into()
            .map_err(|_| AggregateError::InvalidSignature)?;
        if !lean_sphincs::verify(public_key, message, signature) {
            return Err(AggregateError::InvalidSignature);
        }
        self.signatures.push((
            LeanSphincsPublicKey::from_bytes(&public_key.0),
            message.0,
            LeanSphincsSignature::from_bytes(bytes),
        ));
        Ok(())
    }

    /// Moves a checked child into this node without copying its proof buffers.
    ///
    /// Returns [`AggregateError::InvalidInput`] if [`MAX_RECURSIONS`] children
    /// are already present. Callers can aggregate a full node before adding more.
    /// The child is consumed even on rejection.
    pub fn add_child(&mut self, child: Aggregate) -> Result<(), AggregateError> {
        if self.children.len() == MAX_RECURSIONS {
            return Err(AggregateError::InvalidInput(
                "more than MAX_RECURSIONS children",
            ));
        }
        self.children.push((child.claims.inner, child.proof));
        Ok(())
    }

    /// Proves the union of inputs, or exactly `retained` when it is `Some`.
    ///
    /// Call [`crate::setup`] once before proving. This consumes the inputs and
    /// runs blocking reference proving work; concurrent proving calls serialize
    /// in the backend. `log_inv_rate` has the reference's supported range.
    ///
    /// Returns the reference [`AggregateError`] for uncovered output claims,
    /// empty output, unsupported rates or proving failure. Pruning needs the
    /// children's proofs and claims, not their original signatures. No extra
    /// native verification or proof serialization is performed here.
    pub fn prove(
        self,
        retained: Option<&Claims>,
        log_inv_rate: usize,
    ) -> Result<Aggregate, AggregateError> {
        let output = retained.map_or(OutputClaims::All, |claims| {
            OutputClaims::Only(&claims.inner)
        });
        let (claims, proof) = lean_vm::aggregate(
            &self.children,
            vec![],
            self.signatures,
            None,
            output,
            log_inv_rate,
        )?;
        Ok(Aggregate {
            claims: Claims { inner: claims },
            proof,
        })
    }
}
