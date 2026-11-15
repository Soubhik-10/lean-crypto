//! Signature verification across the FORS key and three hypertree layers.

use crate::{
    fors::recover_fors,
    hash::{Address, message_digest},
    signature::Reader,
    tree::climb,
    wots::recover_wots,
};
use alloy_primitives::{B128, B256};

const LAYER_HEIGHTS: [u32; 3] = [8, 8, 10];
// FIPS 205 address domain for hypertree nodes.
const HYPERTREE: u32 = 2;

pub(super) fn recover_root(public_key: &B256, message: &B256, signature: &[u8]) -> Option<B128> {
    let mut reader = Reader::new(signature);
    let digest = message_digest(public_key, message, reader.take()?);
    // FIPS 205 Algorithm 19: 30 FORS bytes, an 18-bit tree, then an 8-bit leaf.
    // The six unused high bits of byte 30 are deliberately discarded.
    let tree = u32::from_be_bytes([0, digest[30], digest[31], digest[32]]) & ((1 << 18) - 1);
    let mut index = u64::from((tree << 8) | u32::from(digest[33]));
    let mut address = Address::new(public_key);
    address.set_tree(0, u64::from(tree));
    let mut node = recover_fors(&mut address, &mut reader, &digest, u32::from(digest[33]))?;

    for (layer, height) in LAYER_HEIGHTS.into_iter().enumerate() {
        let leaf = (index & ((1 << height) - 1)) as u32;
        index >>= height;
        address.set_tree(layer as u32, index);
        node = recover_wots(&mut address, &mut reader, leaf, node)?;
        address.set_domain(HYPERTREE, 0);
        node = climb(&mut address, &mut reader, leaf, height, node)?;
    }
    reader.is_empty().then_some(node)
}
