//! Expected public claims, separate from the proof bytes.

use alloc::vec::Vec;
use alloy_primitives::B256;

/// Exact public statement of an aggregate, in the reference's field order.
///
/// Both signature lists must be strictly sorted `(public_key, message)` pairs,
/// without duplicates. Reconstruct the expected claims independently of the
/// proof sender. Messages are exact 32-byte digests; transaction hashing and
/// signing domains are the caller's responsibility.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AggregateClaims {
    /// leanXMSS public keys (`merkle_root || public_param`) and signed messages.
    pub lean_xmss: Vec<(B256, B256)>,
    /// leanSPHINCS public keys (`PK.seed || PK.root`) and signed messages.
    pub lean_sphincs: Vec<(B256, B256)>,
    /// Optional LeanDA root, including the reference membership-challenge binding.
    pub da_commitment: Option<B256>,
}

impl AggregateClaims {
    pub(crate) fn is_sorted(&self) -> bool {
        self.lean_xmss.windows(2).all(|pair| pair[0] < pair[1])
            && self.lean_sphincs.windows(2).all(|pair| pair[0] < pair[1])
    }
}
