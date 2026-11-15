//! Parameters of the pinned leanSPHINCS configuration.

pub(crate) const NODE_BYTES: usize = 16;
pub(crate) const FORS_TREES: usize = 24;
pub(crate) const FORS_HEIGHT: u32 = 10;
pub(crate) const WOTS_CHAINS: usize = 64;
pub(crate) const CHAIN_END: u8 = 3;
pub(crate) const TARGET_SUM: u16 = 128;
pub(crate) const LAYER_HEIGHTS: [u32; 3] = [8, 8, 10];
pub(crate) const MAX_TREE_HEIGHT: usize = LAYER_HEIGHTS[2] as usize;
pub(crate) const FORS_OPENING_BYTES: usize = NODE_BYTES * (FORS_HEIGHT as usize + 1);
pub(crate) const FORS_BYTES: usize = FORS_TREES * FORS_OPENING_BYTES;
pub(crate) const WOTS_BYTES: usize = 4 + WOTS_CHAINS * NODE_BYTES;
pub(crate) const SEED_TAG: &[u8; 11] = b"leanSPHINCS";
