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

fn leaf_position(digest: &[u8; 34], tree_index: usize) -> u32 {
    let bit = tree_index * FORS_HEIGHT as usize;
    let at = bit / 8;
    let field = u32::from_be_bytes([0, digest[at], digest[at + 1], digest[at + 2]]);
    let leaf = (field >> (24 - FORS_HEIGHT - (bit % 8) as u32)) & ((1 << FORS_HEIGHT) - 1);
    // FORS node indices count across all trees at each height.
    ((tree_index as u32) << FORS_HEIGHT) | leaf
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "sse2")))]
fn recover_trees(
    address: &mut HashContext,
    reader: &mut Reader<'_>,
    digest: &[u8; 34],
    roots: &mut Keccak256,
) -> Option<()> {
    let mut tree_index = 0;
    while tree_index < FORS_TREES {
        let position = leaf_position(digest, tree_index);
        address.set_position(0, position);
        let node = address.hash_node(reader.take()?);
        roots.update(crate::tree::climb(
            address,
            reader,
            position,
            FORS_HEIGHT,
            node,
        )?);
        tree_index += 1;
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
    let mut tree_index = 0;
    while tree_index < FORS_TREES {
        let openings = reader
            .take::<BATCH_BYTES>()?
            .as_chunks::<FORS_OPENING_BYTES>()
            .0
            .first_chunk::<VERIFY_BATCH_WIDTH>()?;
        let positions = core::array::from_fn(|lane| leaf_position(digest, tree_index + lane));
        let nodes = recover_batch(&mut addresses, openings, positions);
        crate::hash::append_nodes(roots, &nodes);
        tree_index += VERIFY_BATCH_WIDTH;
    }
    Some(())
}

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
fn recover_batch(
    addresses: &mut [HashContext; crate::hash::VERIFY_BATCH_WIDTH],
    openings: &[[u8; FORS_OPENING_BYTES]; crate::hash::VERIFY_BATCH_WIDTH],
    mut positions: [u32; crate::hash::VERIFY_BATCH_WIDTH],
) -> [B128; crate::hash::VERIFY_BATCH_WIDTH] {
    HashContext::set_positions(addresses, 0, positions);
    let first =
        core::array::from_fn(|lane| B128::new(openings[lane].as_chunks::<NODE_BYTES>().0[0]));
    let mut nodes = HashContext::hash_nodes(addresses, first);
    let mut level = 0;
    while level < FORS_HEIGHT {
        level += 1;
        let parents = core::array::from_fn(|lane| positions[lane] >> 1);
        HashContext::set_positions(addresses, level, parents);
        let siblings = core::array::from_fn(|lane| {
            B128::new(openings[lane].as_chunks::<NODE_BYTES>().0[level as usize])
        });
        nodes = HashContext::hash_parents(addresses, &nodes, siblings, positions);
        positions = parents;
    }
    nodes
}

pub(crate) fn sign(
    address: &mut HashContext,
    seed: &B256,
    digest: &[u8; 34],
    key_pair: u32,
    output: &mut [u8],
) -> B128 {
    address.set_domain(FORS_PUBLIC_KEY, key_pair);
    let mut roots = address.accumulator();
    let mut tree_index = 0;
    while tree_index < FORS_TREES {
        let bit = tree_index * FORS_HEIGHT as usize;
        let at = bit / 8;
        let field = u32::from_be_bytes([0, digest[at], digest[at + 1], digest[at + 2]]);
        let selected = (field >> (24 - FORS_HEIGHT - (bit % 8) as u32)) & ((1 << FORS_HEIGHT) - 1);
        let mut path = [B128::ZERO; FORS_HEIGHT as usize];
        let (root, secret) = crate::tree::build_tree(
            address,
            seed,
            crate::tree::TreeKind::Fors {
                tree_index: tree_index as u32,
                key_pair,
            },
            FORS_HEIGHT,
            selected,
            &mut path,
        );
        let opening =
            &mut output[tree_index * FORS_OPENING_BYTES..(tree_index + 1) * FORS_OPENING_BYTES];
        opening[..NODE_BYTES].copy_from_slice(secret.as_slice());
        crate::signature::write_nodes(&mut opening[NODE_BYTES..], &path);
        roots.update(root);
        tree_index += 1;
    }
    truncate(roots.finalize())
}
