//! Signature verification across the FORS key and three hypertree layers.

use crate::{
    fors::recover_fors,
    hash::{HashContext, message_digest},
    params::LAYER_HEIGHTS,
    signature::Reader,
    tree::climb,
    wots::recover_wots,
};
use alloy_primitives::{B128, B256};

// FIPS 205 address domain for hypertree nodes.
const HYPERTREE: u32 = 2;

pub(super) fn recover_root(public_key: &B256, message: &B256, bytes: &[u8]) -> Option<B128> {
    let mut reader = Reader::new(bytes);
    let digest = message_digest(public_key, message, reader.take()?);
    // FIPS 205 Algorithm 19: 30 FORS bytes, an 18-bit tree, then an 8-bit leaf.
    // The six unused high bits of byte 30 are deliberately discarded.
    let tree = u32::from_be_bytes([0, digest[30], digest[31], digest[32]]) & ((1 << 18) - 1);
    let mut index = u64::from((tree << 8) | u32::from(digest[33]));
    let mut address = HashContext::new(public_key);
    address.set_tree(0, u64::from(tree));
    let mut node = recover_fors(&mut address, &mut reader, &digest, u32::from(digest[33]))?;

    // Keep the three fallible layer calls outside a loop so the Rust-to-Lean
    // translation retains each early rejection as ordinary function control flow.
    node = recover_layer(
        &mut address,
        &mut reader,
        &mut index,
        0,
        LAYER_HEIGHTS[0],
        node,
    )?;
    node = recover_layer(
        &mut address,
        &mut reader,
        &mut index,
        1,
        LAYER_HEIGHTS[1],
        node,
    )?;
    node = recover_layer(
        &mut address,
        &mut reader,
        &mut index,
        2,
        LAYER_HEIGHTS[2],
        node,
    )?;
    reader.is_empty().then_some(node)
}

#[inline(always)]
fn recover_layer(
    address: &mut HashContext,
    reader: &mut Reader<'_>,
    index: &mut u64,
    layer: u32,
    height: u32,
    node: B128,
) -> Option<B128> {
    let leaf = crate::params::take_layer(index, height);
    address.set_tree(layer, *index);
    let node = recover_wots(address, reader, leaf, node)?;
    address.set_domain(HYPERTREE, 0);
    climb(address, reader, leaf, height, node)
}
