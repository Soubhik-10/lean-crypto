//! Merkle authentication-path recovery shared by FORS and the hypertree.

use crate::{hash::Address, signature::Reader};
use alloy_primitives::B128;

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
