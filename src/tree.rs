//! Streaming Merkle construction, authentication paths and top-tree caching.

use crate::{
    hash::Address,
    params::{LAYER_HEIGHTS, MAX_TREE_HEIGHT},
    signature::Reader,
    wots,
};
use alloy_primitives::{B128, B256};

pub(crate) fn climb(
    address: &mut Address,
    reader: &mut Reader<'_>,
    mut position: u32,
    height: u32,
    mut node: B128,
) -> Option<B128> {
    for level in 1..=height {
        address.set_position(level, position >> 1);
        node = address.hash_parent(&node, reader.take()?, position & 1 != 0);
        position >>= 1;
    }
    Some(node)
}

const HYPERTREE: u32 = 2;
const TOP_LEAVES: usize = 1 << MAX_TREE_HEIGHT;

pub(crate) fn build_tree(
    address: &mut Address,
    height: u32,
    target: u32,
    path: &mut [B128],
    mut leaf: impl FnMut(&mut Address, u32) -> B128,
    mut parent: impl FnMut(&mut Address, u32, u32, &B128, &B128) -> B128,
) -> B128 {
    let mut stack = [B128::ZERO; MAX_TREE_HEIGHT + 1];
    for index in 0..1 << height {
        let mut node = leaf(address, index);
        let mut level = 0;
        let mut position = index;
        loop {
            if position == (target >> level) ^ 1
                && let Some(sibling) = path.get_mut(level as usize)
            {
                *sibling = node;
            }
            if level == height || position & 1 == 0 {
                stack[level as usize] = node;
                break;
            }
            node = parent(
                address,
                level + 1,
                position >> 1,
                &stack[level as usize],
                &node,
            );
            position >>= 1;
            level += 1;
        }
    }
    stack[height as usize]
}

pub(crate) fn build_xmss(
    address: &mut Address,
    seed: &B256,
    height: u32,
    target: u32,
    path: &mut [B128],
) -> B128 {
    build_tree(
        address,
        height,
        target,
        path,
        |address, index| wots::public_leaf(address, seed, index),
        |address, height, index, left, right| {
            address.set_domain(HYPERTREE, 0);
            address.set_position(height, index);
            address.hash_parent(left, &right.0, false)
        },
    )
}

// Public nodes only. Retaining every level lets signing select a path after H_msg
// derives the leaf index from the public root.
pub(crate) struct TopTree {
    nodes: [B128; 2 * TOP_LEAVES],
}

impl TopTree {
    pub(crate) fn new(address: &mut Address, seed: &B256) -> Self {
        address.set_tree((LAYER_HEIGHTS.len() - 1) as u32, 0);
        let mut nodes = [B128::ZERO; 2 * TOP_LEAVES];
        for index in 0..TOP_LEAVES {
            nodes[TOP_LEAVES + index] = wots::public_leaf(address, seed, index as u32);
        }
        let mut width = TOP_LEAVES / 2;
        for height in 1..=MAX_TREE_HEIGHT {
            for index in 0..width {
                let at = width + index;
                address.set_domain(HYPERTREE, 0);
                address.set_position(height as u32, index as u32);
                nodes[at] = address.hash_parent(&nodes[2 * at], &nodes[2 * at + 1].0, false);
            }
            width >>= 1;
        }
        Self { nodes }
    }

    pub(crate) fn root(&self) -> B128 {
        self.nodes[1]
    }

    pub(crate) fn path(&self, leaf: u32) -> [B128; MAX_TREE_HEIGHT] {
        core::array::from_fn(|level| self.nodes[((TOP_LEAVES + leaf as usize) >> level) ^ 1])
    }
}
