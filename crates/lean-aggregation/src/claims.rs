//! Canonical leanSPHINCS claim sets in the reference's order.

use lean_sphincs::B256;
use lean_vm::{AggregateClaims, lean_sphincs::LeanSphincsPublicKey};

/// A sorted, deduplicated set of `(public_key, message)` claims.
///
/// Keys are `PK.seed || PK.root`; messages are the exact signed digests. This
/// type performs no transaction hashing or domain separation. Construct expected
/// claims independently from the transactions being verified, not from a sender's
/// untrusted declaration.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Claims {
    pub(crate) inner: AggregateClaims,
}

impl Claims {
    /// Canonicalizes claims in reference `(public_key, message)` order.
    /// Duplicate claims denote the same signature obligation and are removed.
    pub fn new(claims: impl IntoIterator<Item = (B256, B256)>) -> Self {
        let mut lean_sphincs: Vec<_> = claims
            .into_iter()
            .map(|(public_key, message)| {
                (LeanSphincsPublicKey::from_bytes(&public_key.0), message.0)
            })
            .collect();
        lean_sphincs.sort_unstable();
        lean_sphincs.dedup();
        Self {
            inner: AggregateClaims {
                lean_sphincs,
                ..Default::default()
            },
        }
    }

    /// Returns the number of distinct `(public_key, message)` pairs.
    pub fn len(&self) -> usize {
        self.inner.lean_sphincs.len()
    }

    /// Returns whether there are no signature obligations.
    pub fn is_empty(&self) -> bool {
        self.inner.lean_sphincs.is_empty()
    }

    /// Iterates in canonical order without allocating a second claim list.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (B256, B256)> + '_ {
        self.inner
            .lean_sphincs
            .iter()
            .map(|(public_key, message)| (B256::new(public_key.to_bytes()), B256::new(*message)))
    }
}
