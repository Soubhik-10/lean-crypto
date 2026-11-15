//! WOTS+C codeword validation and public-key recovery.

use crate::{
    hash::{Address, truncate},
    signature::Reader,
};
use alloy_primitives::B128;

const WOTS_CHAINS: usize = 64;
const CHAIN_END: u8 = 3;
const TARGET_SUM: u16 = 128;

// FIPS 205 chain/key domains and leanSPHINCS's WOTS+C encoding domain.
const WOTS_CHAIN: u32 = 0;
const WOTS_PUBLIC_KEY: u32 = 1;
const WOTS_ENCODING: u32 = 7;

pub(crate) fn recover_wots(
    address: &mut Address,
    reader: &mut Reader<'_>,
    key_pair: u32,
    message: B128,
) -> Option<B128> {
    address.set_domain(WOTS_ENCODING, key_pair);
    let code = address.encode(&message, reader.take()?);
    let digits: [u8; WOTS_CHAINS] =
        core::array::from_fn(|i| (code[i / 4] >> (6 - 2 * (i % 4))) & 3);
    if digits.iter().map(|&digit| u16::from(digit)).sum::<u16>() != TARGET_SUM {
        return None;
    }

    address.set_domain(WOTS_PUBLIC_KEY, key_pair);
    let mut ends = address.accumulator();
    address.set_domain(WOTS_CHAIN, key_pair);
    for (chain, digit) in digits.into_iter().enumerate() {
        let mut value = B128::new(*reader.take()?);
        for step in digit..CHAIN_END {
            address.set_position(chain as u32, u32::from(step));
            value = address.hash_node(&value.0);
        }
        ends.update(value);
    }
    Some(truncate(ends.finalize()))
}
