//! FORS public-key recovery from serialized tree openings.

use crate::{
    hash::{Address, truncate},
    signature::Reader,
};
use alloy_primitives::{B128, Keccak256};

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
    address.set_domain(FORS_TREE, key_pair);
    recover_trees(address, reader, digest, &mut roots)?;
    Some(truncate(roots.finalize()))
}

fn leaf_position(digest: &[u8; 34], tree: usize) -> u32 {
    let bit = tree * FORS_HEIGHT as usize;
    let at = bit / 8;
    let field = u32::from_be_bytes([0, digest[at], digest[at + 1], digest[at + 2]]);
    let leaf = (field >> (24 - FORS_HEIGHT - (bit % 8) as u32)) & ((1 << FORS_HEIGHT) - 1);
    // FORS node indices count across all trees at each height.
    ((tree as u32) << FORS_HEIGHT) | leaf
}

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "sse2",
    not(target_feature = "avx2")
)))]
fn recover_trees(
    address: &mut Address,
    reader: &mut Reader<'_>,
    digest: &[u8; 34],
    roots: &mut Keccak256,
) -> Option<()> {
    for tree in 0..FORS_TREES {
        let position = leaf_position(digest, tree);
        address.set_position(0, position);
        let node = address.hash_node(reader.take()?);
        roots.update(crate::tree::climb(
            address,
            reader,
            position,
            FORS_HEIGHT,
            node,
        )?);
    }
    Some(())
}

// The baseline x86-64 Keccak backend hashes one input at a time. SSE2 can
// process a pair of independent FORS openings without changing root order.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "sse2",
    not(target_feature = "avx2")
))]
fn recover_trees(
    address: &mut Address,
    reader: &mut Reader<'_>,
    digest: &[u8; 34],
    roots: &mut Keccak256,
) -> Option<()> {
    use crate::hash::NODE_BYTES;

    const OPENING_NODES: usize = 1 + FORS_HEIGHT as usize;
    const OPENING_BYTES: usize = OPENING_NODES * NODE_BYTES;
    const { assert!(FORS_TREES.is_multiple_of(2)) };

    let mut addresses = [address.clone(), address.clone()];
    for tree in (0..FORS_TREES).step_by(2) {
        let first = reader.take::<OPENING_BYTES>()?.as_chunks::<NODE_BYTES>().0;
        let second = reader.take::<OPENING_BYTES>()?.as_chunks::<NODE_BYTES>().0;
        let [first_secret, first_path @ ..] = first.first_chunk::<OPENING_NODES>()?;
        let [second_secret, second_path @ ..] = second.first_chunk::<OPENING_NODES>()?;
        let mut positions = [leaf_position(digest, tree), leaf_position(digest, tree + 1)];
        for (address, position) in addresses.iter_mut().zip(positions) {
            address.set_position(0, position);
        }
        let mut nodes = Address::hash_node_pair(&mut addresses, [first_secret, second_secret]);
        for (level, (first, second)) in first_path.iter().zip(second_path).enumerate() {
            let parents = positions.map(|position| position >> 1);
            for (address, parent) in addresses.iter_mut().zip(parents) {
                address.set_position(level as u32 + 1, parent);
            }
            nodes = Address::hash_parent_pair(&mut addresses, &nodes, [first, second], positions);
            positions = parents;
        }
        for node in nodes {
            roots.update(node);
        }
    }
    Some(())
}
