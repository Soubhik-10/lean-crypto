//! FORS public-key recovery from serialized tree openings.

use crate::{
    hash::{Address, truncate},
    signature::Reader,
    tree::climb,
};
use alloy_primitives::B128;

const FORS_TREES: usize = 24;
const FORS_HEIGHT: u32 = 10;

// FIPS 205 address domains for FORS nodes and root compression.
const FORS_TREE: u32 = 3;
const FORS_PUBLIC_KEY: u32 = 4;

pub(crate) fn recover_fors(
    address: &mut Address,
    reader: &mut Reader<'_>,
    digest: &[u8; 34],
    key_pair: u32,
) -> Option<B128> {
    address.set_domain(FORS_PUBLIC_KEY, key_pair);
    let mut roots = address.accumulator();
    for tree in 0..FORS_TREES {
        let bit = tree * FORS_HEIGHT as usize;
        let at = bit / 8;
        let field = u32::from_be_bytes([0, digest[at], digest[at + 1], digest[at + 2]]);
        let leaf = (field >> (24 - FORS_HEIGHT - (bit % 8) as u32)) & ((1 << FORS_HEIGHT) - 1);
        // FORS node indices count across all 24 trees, at each height.
        let position = ((tree as u32) << FORS_HEIGHT) | leaf;
        address.set_domain(FORS_TREE, key_pair);
        address.set_position(0, position);
        let node = address.hash_node(reader.take()?);
        roots.update(climb(address, reader, position, FORS_HEIGHT, node)?);
    }
    Some(truncate(roots.finalize()))
}
