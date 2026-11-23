//! Prepared fixed-program aggregate verification without the prover or compiler.

use crate::{AggregateClaims, AggregateProof, PROGRAM_IV, PROGRAM_WORDS, VerifyError, vm};
use alloy_primitives::Keccak256;

/// Prepared verifier for the pinned aggregate program.
///
/// Preparation validates the supplied program against [`PROGRAM_IV`] before
/// allocating the sparse evaluation tables. The context retains no prover,
/// compiler, thread pool or copy of the original stacked bytecode. Reuse it
/// across proofs. Verification takes shared references and does not mutate it.
#[derive(Debug)]
pub struct Verifier {
    bytecode: vm::Bytecode,
}

impl Verifier {
    /// Checks and prepares the exact pinned program's stacked u64 bytecode.
    ///
    /// The program can come from an untrusted source: its length and fingerprint
    /// must match the pinned profile. Words use the reference's LSB-first table
    /// order; deserialize stored words as little-endian u64s. Returns
    /// [`VerifyError::Program`] for a different program, before preparing tables.
    pub fn new(stacked_bytecode: &[u64]) -> Result<Self, VerifyError> {
        if stacked_bytecode.len() != PROGRAM_WORDS {
            return Err(VerifyError::Program);
        }
        let bytecode = vm::Bytecode::new(stacked_bytecode, Some(PROGRAM_IV))
            .map_err(|_| VerifyError::Program)?;
        Ok(Self { bytecode })
    }

    /// Verifies the full aggregate against exactly the expected public claims.
    ///
    /// Includes strict claim order, both scheme-list digests, the optional DA
    /// binding, fixed program/transcript identity, deferred bytecode evaluation,
    /// and every VM, Merkle, sumcheck, GKR, grinding and WHIR check. There is no
    /// unchecked replay mode. Callers must bound untrusted claim counts and proof
    /// bytes before preparing inputs; this library does not impose network policy.
    pub fn verify(
        &self,
        claims: &AggregateClaims,
        proof: &AggregateProof,
    ) -> Result<(), VerifyError> {
        if !claims.is_sorted() {
            return Err(VerifyError::Claims);
        }
        // Every tag slot of the pinned program is zero, including the first word.
        let value = if proof.point.iter().all(|value| *value == vm::E::new(0, 0)) {
            vm::E::new(0, 0)
        } else {
            self.bytecode
                .evaluate(&proof.point)
                .map_err(|_| VerifyError::Proof)?
        };
        let mut statement = Keccak256::new();
        statement.update(self.bytecode.fiat_shamir_iv());
        for list in [&claims.lean_xmss, &claims.lean_sphincs] {
            let mut hash = Keccak256::new();
            for (key, message) in list {
                hash.update(key.as_slice());
                hash.update(message.as_slice());
            }
            statement.update(hash.finalize());
        }
        statement.update(vm::da::digest(claims.da_commitment.map(|root| root.0)));
        for coordinate in proof.point.iter().chain(core::iter::once(&value)) {
            statement.update(coordinate.c0.to_le_bytes());
            statement.update(coordinate.c1.to_le_bytes());
        }
        let public_input = statement.finalize();
        vm::verify_execution(&self.bytecode, &public_input.0, &proof.execution)
            .map_err(|_| VerifyError::Proof)
    }
}
