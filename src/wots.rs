//! WOTS+C signing, codeword validation and public-key recovery.

use crate::{
    hash::{HashContext, truncate},
    params::{CHAIN_END, NODE_BYTES, TARGET_SUM, WOTS_CHAINS},
    signature::Reader,
};
use alloy_primitives::{B128, B256};

// FIPS 205 chain/key domains and leanSPHINCS's WOTS+C encoding domain.
const WOTS_CHAIN: u32 = 0;
const WOTS_PUBLIC_KEY: u32 = 1;
const WOTS_ENCODING: u32 = 7;
const WOTS_PRF: u32 = 5;

pub(crate) fn recover_wots(
    address: &mut HashContext,
    reader: &mut Reader<'_>,
    key_pair: u32,
    message: B128,
) -> Option<B128> {
    address.set_domain(WOTS_ENCODING, key_pair);
    let code = address.encode(&message, reader.take()?);
    let digits = codeword(&code)?;

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

fn codeword(code: &B128) -> Option<[u8; WOTS_CHAINS]> {
    let digits = core::array::from_fn(|i| (code[i / 4] >> (6 - 2 * (i % 4))) & 3);
    (digits.iter().map(|&digit| u16::from(digit)).sum::<u16>() == TARGET_SUM).then_some(digits)
}

fn chain_start(address: &mut HashContext, seed: &B256, key_pair: u32, chain: u32) -> B128 {
    address.set_domain(WOTS_PRF, key_pair);
    address.set_position(chain, 0);
    let secret = address.derive_secret(seed);
    address.set_domain(WOTS_CHAIN, key_pair);
    secret
}

pub(crate) fn public_leaf(address: &mut HashContext, seed: &B256, key_pair: u32) -> B128 {
    address.set_domain(WOTS_PUBLIC_KEY, key_pair);
    let mut ends = address.accumulator();
    for chain in 0..WOTS_CHAINS {
        let mut node = chain_start(address, seed, key_pair, chain as u32);
        for step in 0..CHAIN_END {
            address.set_position(chain as u32, u32::from(step));
            node = address.hash_node(&node.0);
        }
        ends.update(node);
    }
    truncate(ends.finalize())
}

pub(crate) fn sign(
    address: &mut HashContext,
    seed: &B256,
    key_pair: u32,
    message: &B128,
    output: &mut [u8],
    counter_limit: u64,
) -> Option<()> {
    address.set_domain(WOTS_ENCODING, key_pair);
    // The least admissible counter is required for deterministic signing.
    let (counter, digits) = (0..counter_limit).find_map(|counter| {
        codeword(&address.encode(message, &(counter as u32).to_be_bytes()))
            .map(|digits| (counter as u32, digits))
    })?;
    output[..4].copy_from_slice(&counter.to_be_bytes());
    for (chain, digit) in digits.into_iter().enumerate() {
        let mut node = chain_start(address, seed, key_pair, chain as u32);
        for step in 0..digit {
            address.set_position(chain as u32, u32::from(step));
            node = address.hash_node(&node.0);
        }
        output[4 + chain * NODE_BYTES..4 + (chain + 1) * NODE_BYTES]
            .copy_from_slice(node.as_slice());
    }
    Some(())
}
