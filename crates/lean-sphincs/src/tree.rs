//! Streaming Merkle construction, authentication paths and top-tree caching.

use crate::{
    hash::HashContext,
    params::{LAYER_HEIGHTS, MAX_TREE_HEIGHT},
    signature::Reader,
    wots,
};
use alloy_primitives::{B128, B256};

pub(crate) fn climb(
    address: &mut HashContext,
    reader: &mut Reader<'_>,
    mut position: u32,
    height: u32,
    mut node: B128,
) -> Option<B128> {
    let mut level = 0;
    while level < height {
        level += 1;
        address.set_position(level, position >> 1);
        node = address.hash_parent(&node, reader.take()?, position & 1 != 0);
        position >>= 1;
    }
    Some(node)
}

const HYPERTREE: u32 = 2;
const FORS_TREE: u32 = 3;
const FORS_PRF: u32 = 6;
const TOP_LEAVES: usize = 1 << MAX_TREE_HEIGHT;

#[derive(Clone, Copy)]
pub(crate) enum TreeKind {
    Xmss,
    Fors { tree_index: u32, key_pair: u32 },
}

fn tree_leaf(address: &mut HashContext, seed: &B256, kind: TreeKind, index: u32) -> (B128, B128) {
    match kind {
        TreeKind::Xmss => (wots::public_leaf(address, seed, index), B128::ZERO),
        TreeKind::Fors {
            tree_index,
            key_pair,
        } => {
            address.set_domain(FORS_PRF, key_pair);
            address.set_position(0, (tree_index << crate::params::FORS_HEIGHT) | index);
            let secret = address.derive_secret(seed);
            address.set_domain(FORS_TREE, key_pair);
            address.set_position(0, (tree_index << crate::params::FORS_HEIGHT) | index);
            (address.hash_node(&secret.0), secret)
        }
    }
}

fn tree_parent(
    address: &mut HashContext,
    kind: TreeKind,
    height: u32,
    index: u32,
    left: &B128,
    right: &B128,
) -> B128 {
    match kind {
        TreeKind::Xmss => {
            address.set_domain(HYPERTREE, 0);
            address.set_position(height, index);
        }
        TreeKind::Fors {
            tree_index,
            key_pair,
        } => {
            address.set_domain(FORS_TREE, key_pair);
            address.set_position(
                height,
                (tree_index << (crate::params::FORS_HEIGHT - height)) | index,
            );
        }
    }
    address.hash_parent(left, &right.0, false)
}

// Visit both children before their parent, with recursion bounded by the
// production tree heights (at most MAX_TREE_HEIGHT).
fn build_subtree(
    address: &mut HashContext,
    seed: &B256,
    kind: TreeKind,
    position: (u32, u32),
    target: u32,
    path: &mut [B128],
) -> (B128, B128) {
    let (height, index) = position;
    let (node, selected_secret) = if height == 0 {
        let (leaf, secret) = tree_leaf(address, seed, kind, index);
        (leaf, if index == target { secret } else { B128::ZERO })
    } else {
        let child_height = height - 1;
        let (left, left_secret) =
            build_subtree(address, seed, kind, (child_height, index * 2), target, path);
        let (right, right_secret) = build_subtree(
            address,
            seed,
            kind,
            (child_height, index * 2 + 1),
            target,
            path,
        );
        let node = tree_parent(address, kind, height, index, &left, &right);
        let secret = if (target >> child_height) & 1 == 0 {
            left_secret
        } else {
            right_secret
        };
        (node, secret)
    };
    if index == (target >> height) ^ 1
        && let Some(sibling) = path.get_mut(height as usize)
    {
        *sibling = node;
    }
    (node, selected_secret)
}

#[inline(always)]
pub(crate) fn build_tree(
    address: &mut HashContext,
    seed: &B256,
    kind: TreeKind,
    height: u32,
    target: u32,
    path: &mut [B128],
) -> (B128, B128) {
    build_subtree(address, seed, kind, (height, 0), target, path)
}

pub(crate) fn build_xmss(
    address: &mut HashContext,
    seed: &B256,
    height: u32,
    target: u32,
    path: &mut [B128],
) -> B128 {
    build_tree(address, seed, TreeKind::Xmss, height, target, path).0
}

// Public nodes only. Retaining every level lets signing select a path after H_msg
// derives the leaf index from the public root.
pub(crate) struct TopTree {
    nodes: [B128; 2 * TOP_LEAVES],
}

impl TopTree {
    pub(crate) fn new(address: &mut HashContext, seed: &B256) -> Self {
        address.set_tree((LAYER_HEIGHTS.len() - 1) as u32, 0);
        let mut nodes = [B128::ZERO; 2 * TOP_LEAVES];
        let mut index = 0;
        while index < TOP_LEAVES {
            nodes[TOP_LEAVES + index] = wots::public_leaf(address, seed, index as u32);
            index += 1;
        }
        let mut width = TOP_LEAVES / 2;
        let mut height = 0;
        while height < MAX_TREE_HEIGHT {
            height += 1;
            let mut index = 0;
            while index < width {
                let at = width + index;
                address.set_domain(HYPERTREE, 0);
                address.set_position(height as u32, index as u32);
                nodes[at] = address.hash_parent(&nodes[2 * at], &nodes[2 * at + 1].0, false);
                index += 1;
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
