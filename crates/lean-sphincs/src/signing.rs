//! Deterministic signing and public-key derivation from a 32-byte secret seed.

use crate::{
    Signature, fors,
    hash::{HashContext, message_digest, truncate},
    params::{FORS_BYTES, LAYER_HEIGHTS, MAX_TREE_HEIGHT, NODE_BYTES, SEED_TAG, WOTS_BYTES},
    tree::{TopTree, build_xmss},
    wots,
};
use alloy_primitives::{B128, B256, keccak256_uncached};
use core::fmt;

const COUNTER_LIMIT: u64 = 1 << 32;

/// A signing operation could not find an admissible WOTS+C encoding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SignError {
    /// All 32-bit counters were exhausted for the given hypertree layer.
    CounterExhausted {
        /// Layer index, counted from the bottom (0, 1 or 2).
        layer: u8,
    },
}

impl fmt::Display for SignError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CounterExhausted { layer } => {
                write!(f, "no admissible WOTS+C counter for layer {layer}")
            }
        }
    }
}

impl core::error::Error for SignError {}

/// Derives a public key, encoded as `PK.seed || PK.root`, from a secret seed.
///
/// The caller must generate the seed from 32 uniformly random bytes and keep it
/// secret. This function does not generate randomness or retain the seed.
pub fn key_gen(secret_seed: &B256) -> B256 {
    let (pk_seed, _) = expand_key(secret_seed);
    let mut public_key = B256::ZERO;
    public_key[..NODE_BYTES].copy_from_slice(pk_seed.as_slice());
    let mut address = HashContext::new(&public_key);
    address.set_tree(2, 0);
    let mut path = [];
    let root = build_xmss(
        &mut address,
        secret_seed,
        MAX_TREE_HEIGHT as u32,
        0,
        &mut path,
    );
    public_key[NODE_BYTES..].copy_from_slice(root.as_slice());
    public_key
}

/// Signs an exact 32-byte message digest using a secret seed.
///
/// Signing is deterministic. The caller supplies the signing domain and must
/// limit each seed to at most `2^30` signed messages, including attestations.
/// This function does not track that budget or generate randomness. The top tree
/// is built once and reused for its root and authentication path. Its cache
/// occupies approximately 32 KiB of stack memory; no heap allocation is needed.
///
/// # Errors
///
/// Returns [`SignError::CounterExhausted`] if all 32-bit encoding counters for a
/// layer are exhausted. No partial signature is returned.
pub fn sign(secret_seed: &B256, message: &B256) -> Result<Signature, SignError> {
    sign_with_limit(secret_seed, message, COUNTER_LIMIT)
}

fn expand_key(seed: &B256) -> (B128, B256) {
    let mut input = [0; SEED_TAG.len() + 32 + 1];
    input[..SEED_TAG.len()].copy_from_slice(SEED_TAG);
    input[SEED_TAG.len()..SEED_TAG.len() + 32].copy_from_slice(seed.as_slice());
    // The hash input contains the seed and must bypass Alloy's global cache.
    let pk_seed = truncate(keccak256_uncached(input));
    input[SEED_TAG.len() + 32] = 1;
    (pk_seed, keccak256_uncached(input))
}

fn randomizer(sk_prf: &B256, pk_seed: &B128, message: &B256) -> B128 {
    let mut input = [0; 32 + NODE_BYTES + 2 + SEED_TAG.len() + 32];
    input[..32].copy_from_slice(sk_prf.as_slice());
    input[32..48].copy_from_slice(pk_seed.as_slice());
    input[49] = SEED_TAG.len() as u8;
    input[50..50 + SEED_TAG.len()].copy_from_slice(SEED_TAG);
    input[50 + SEED_TAG.len()..].copy_from_slice(message.as_slice());
    truncate(keccak256_uncached(input))
}

fn sign_with_limit(
    seed: &B256,
    message: &B256,
    counter_limit: u64,
) -> Result<Signature, SignError> {
    let (pk_seed, sk_prf) = expand_key(seed);
    let mut public_key = B256::ZERO;
    public_key[..NODE_BYTES].copy_from_slice(pk_seed.as_slice());
    let mut address = HashContext::new(&public_key);
    let top = TopTree::new(&mut address, seed);
    public_key[NODE_BYTES..].copy_from_slice(top.root().as_slice());

    let rho = randomizer(&sk_prf, &pk_seed, message);
    let digest = message_digest(&public_key, message, &rho.0);
    let tree_index = u32::from_be_bytes([0, digest[30], digest[31], digest[32]]) & ((1 << 18) - 1);
    let mut index = u64::from((tree_index << 8) | u32::from(digest[33]));
    let mut serialized = Signature::ZERO;
    serialized[..NODE_BYTES].copy_from_slice(rho.as_slice());
    address.set_tree(0, u64::from(tree_index));
    let mut node = fors::sign(
        &mut address,
        seed,
        &digest,
        u32::from(digest[33]),
        &mut serialized[NODE_BYTES..NODE_BYTES + FORS_BYTES],
    );
    let mut offset = NODE_BYTES + FORS_BYTES;
    let mut layer = 0;
    while layer < LAYER_HEIGHTS.len() {
        let height = LAYER_HEIGHTS[layer];
        let leaf = crate::params::take_layer(&mut index, height);
        address.set_tree(layer as u32, index);
        let layer_bytes = WOTS_BYTES + height as usize * NODE_BYTES;
        let output = &mut serialized[offset..offset + layer_bytes];
        wots::sign(
            &mut address,
            seed,
            leaf,
            &node,
            &mut output[..WOTS_BYTES],
            counter_limit,
        )
        .ok_or(SignError::CounterExhausted { layer: layer as u8 })?;
        let mut path = [B128::ZERO; MAX_TREE_HEIGHT];
        if layer == LAYER_HEIGHTS.len() - 1 {
            path = top.path(leaf);
        } else {
            node = build_xmss(
                &mut address,
                seed,
                height,
                leaf,
                &mut path[..height as usize],
            );
        }
        crate::signature::write_nodes(&mut output[WOTS_BYTES..], &path);
        offset += layer_bytes;
        layer += 1;
    }
    Ok(serialized)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exhausted_counter_budget_returns_an_error() {
        assert_eq!(
            sign_with_limit(&B256::ZERO, &B256::ZERO, 0),
            Err(SignError::CounterExhausted { layer: 0 })
        );
    }
}
