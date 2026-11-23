//! Canonical leanSPHINCS claim sets in the reference's order.

use alloc::vec::Vec;
use lean_sphincs::B256;

#[cfg(feature = "std")]
use lean_vm::{AggregateClaims, lean_sphincs::LeanSphincsPublicKey};

/// A sorted, deduplicated set of `(public_key, message)` claims.
///
/// Keys are `PK.seed || PK.root`; messages are the exact signed digests. This
/// type performs no transaction hashing or domain separation. Construct expected
/// claims independently from the transactions being verified, not from a sender's
/// untrusted declaration. Available without `std`, using `alloc` for the list.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Claims {
    #[cfg(feature = "std")]
    pub(crate) inner: AggregateClaims,
    #[cfg(not(feature = "std"))]
    inner: Vec<(B256, [u8; 32])>,
}

impl Claims {
    /// Canonicalizes claims in reference `(public_key, message)` order.
    /// Duplicate claims denote the same signature obligation and are removed.
    pub fn new(claims: impl IntoIterator<Item = (B256, B256)>) -> Self {
        #[cfg(feature = "std")]
        let mut lean_sphincs: Vec<_> = claims
            .into_iter()
            .map(|(public_key, message)| {
                (LeanSphincsPublicKey::from_bytes(&public_key.0), message.0)
            })
            .collect();
        #[cfg(not(feature = "std"))]
        let mut lean_sphincs: Vec<_> = claims
            .into_iter()
            .map(|(public_key, message)| (public_key, message.0))
            .collect();
        lean_sphincs.sort_unstable();
        lean_sphincs.dedup();
        Self {
            #[cfg(feature = "std")]
            inner: AggregateClaims {
                lean_sphincs,
                ..Default::default()
            },
            #[cfg(not(feature = "std"))]
            inner: lean_sphincs,
        }
    }

    /// Returns the number of distinct `(public_key, message)` pairs.
    pub fn len(&self) -> usize {
        #[cfg(feature = "std")]
        {
            self.inner.lean_sphincs.len()
        }
        #[cfg(not(feature = "std"))]
        {
            self.inner.len()
        }
    }

    /// Returns whether there are no signature obligations.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterates in canonical order without allocating a second claim list.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (B256, B256)> + '_ {
        #[cfg(feature = "std")]
        {
            self.inner.lean_sphincs.iter().map(|(public_key, message)| {
                (B256::new(public_key.to_bytes()), B256::new(*message))
            })
        }
        #[cfg(not(feature = "std"))]
        {
            self.inner
                .iter()
                .map(|(public_key, message)| (*public_key, B256::new(*message)))
        }
    }
}
