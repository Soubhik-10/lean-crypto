//! FORS signing and public-key recovery from serialized tree openings.

use crate::{
    hash::{Address, truncate},
    params::{FORS_HEIGHT, FORS_OPENING_BYTES, FORS_TREES, NODE_BYTES},
    signature::Reader,
    tree::climb,
};
use alloy_primitives::{B128, B256};

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

const FORS_PRF: u32 = 6;

pub(crate) fn sign(
    address: &mut Address,
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
