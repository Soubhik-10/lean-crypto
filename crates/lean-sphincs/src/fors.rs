//! FORS signing and public-key recovery from serialized tree openings.

use crate::{
    hash::{HashContext, truncate},
    params::{FORS_HEIGHT, FORS_OPENING_BYTES, FORS_TREES, NODE_BYTES},
    signature::Reader,
};
use alloy_primitives::{B128, B256, Keccak256};

// FIPS 205 address domains for FORS nodes and root compression.
const FORS_TREE: u32 = 3;
const FORS_PUBLIC_KEY: u32 = 4;

pub(crate) fn recover_fors(
    address: &mut HashContext,
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

#[cfg(not(all(target_arch = "x86_64", target_feature = "sse2")))]
fn recover_trees(
    address: &mut HashContext,
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

// Independent FORS openings use the target's SIMD width. Compress their roots
// in the same order as the serialized openings.
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
fn recover_trees(
    address: &mut HashContext,
    reader: &mut Reader<'_>,
    digest: &[u8; 34],
    roots: &mut Keccak256,
) -> Option<()> {
    use crate::hash::VERIFY_BATCH_WIDTH;

    const BATCH_BYTES: usize = FORS_OPENING_BYTES * VERIFY_BATCH_WIDTH;
    const { assert!(FORS_TREES.is_multiple_of(VERIFY_BATCH_WIDTH)) };

    let mut addresses = core::array::from_fn(|_| address.clone());
    for tree in (0..FORS_TREES).step_by(VERIFY_BATCH_WIDTH) {
        let openings = reader
            .take::<BATCH_BYTES>()?
            .as_chunks::<FORS_OPENING_BYTES>()
            .0
            .first_chunk::<VERIFY_BATCH_WIDTH>()?
            .each_ref()
            .map(|bytes| bytes.as_chunks::<NODE_BYTES>().0);
        let mut positions = core::array::from_fn(|lane| leaf_position(digest, tree + lane));
        for (address, position) in addresses.iter_mut().zip(positions) {
            address.set_position(0, position);
        }
        let mut nodes = HashContext::hash_nodes(&mut addresses, openings.map(|nodes| &nodes[0]));
        for level in 1..=FORS_HEIGHT {
            let parents = positions.map(|position| position >> 1);
            for (address, parent) in addresses.iter_mut().zip(parents) {
                address.set_position(level, parent);
            }
            let siblings = openings.map(|nodes| &nodes[level as usize]);
            nodes = HashContext::hash_parents(&mut addresses, &nodes, siblings, positions);
            positions = parents;
        }
        for node in nodes {
            roots.update(node);
        }
    }
    Some(())
}

const FORS_PRF: u32 = 6;

pub(crate) fn sign(
    address: &mut HashContext,
    seed: &B256,
    digest: &[u8; 34],
    key_pair: u32,
    output: &mut [u8],
) -> B128 {
    address.set_domain(FORS_PUBLIC_KEY, key_pair);
    let mut roots = address.accumulator();
    for tree in 0..FORS_TREES {
        let bit = tree * FORS_HEIGHT as usize;
        let at = bit / 8;
        let field = u32::from_be_bytes([0, digest[at], digest[at + 1], digest[at + 2]]);
        let selected = (field >> (24 - FORS_HEIGHT - (bit % 8) as u32)) & ((1 << FORS_HEIGHT) - 1);
        let mut secret = B128::ZERO;
        let mut path = [B128::ZERO; FORS_HEIGHT as usize];
        let root = crate::tree::build_tree(
            address,
            FORS_HEIGHT,
            selected,
            &mut path,
            |address, index| {
                address.set_domain(FORS_PRF, key_pair);
                address.set_position(0, ((tree as u32) << FORS_HEIGHT) | index);
                let value = address.derive_secret(seed);
                if index == selected {
                    secret = value;
                }
                address.set_domain(FORS_TREE, key_pair);
                address.set_position(0, ((tree as u32) << FORS_HEIGHT) | index);
                address.hash_node(&value.0)
            },
            |address, height, index, left, right| {
                address.set_domain(FORS_TREE, key_pair);
                address.set_position(height, ((tree as u32) << (FORS_HEIGHT - height)) | index);
                address.hash_parent(left, &right.0, false)
            },
        );
        let opening = &mut output[tree * FORS_OPENING_BYTES..(tree + 1) * FORS_OPENING_BYTES];
        opening[..NODE_BYTES].copy_from_slice(secret.as_slice());
        for (output, node) in opening[NODE_BYTES..].chunks_exact_mut(NODE_BYTES).zip(path) {
            output.copy_from_slice(node.as_slice());
        }
        roots.update(root);
    }
    truncate(roots.finalize())
}
