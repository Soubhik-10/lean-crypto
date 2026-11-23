//! Merkle openings: one full path per query.

use alloc::vec::Vec;

use crate::vm::field::K;
use crate::vm::hash::{Digest, keccak_hash};

pub(crate) fn hash_pair(left: &[u8], right: &[u8]) -> Digest {
    let mut pair = [0u8; 64];
    pair[..32].copy_from_slice(left);
    pair[32..].copy_from_slice(right);
    keccak_hash(&pair)
}

pub(crate) fn hash_leaf(image: &[K]) -> Digest {
    keccak_hash(
        &image
            .iter()
            .flat_map(|word| word.to_bytes())
            .collect::<Vec<u8>>(),
    )
}

/// One query's own opening, the form the Rust and Lean verifiers read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MerklePath {
    pub(crate) leaf_index: u64,
    /// The whole leaf image, its zero prefix included.
    pub(crate) leaf: Vec<K>,
    /// Bottom level first.
    pub(crate) siblings: Vec<[u8; 32]>,
}

impl MerklePath {
    pub(crate) fn root(&self) -> Digest {
        let mut node = hash_leaf(&self.leaf);
        for (level, sibling) in self.siblings.iter().enumerate() {
            node = if self.leaf_index >> level & 1 == 0 {
                hash_pair(&node.0, sibling)
            } else {
                hash_pair(sibling, &node.0)
            };
        }
        node
    }
}
