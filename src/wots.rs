//! WOTS+C signing, codeword validation and public-key recovery.

use crate::{
    hash::{HashContext, truncate},
    params::{CHAIN_END, NODE_BYTES, TARGET_SUM, WOTS_CHAINS},
    signature::Reader,
};
use alloy_primitives::{B128, B256, Keccak256};

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
    recover_chains(address, reader, &digits, &mut ends)?;
    Some(truncate(ends.finalize()))
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
fn recover_chains(
    address: &mut HashContext,
    reader: &mut Reader<'_>,
    digits: &[u8; WOTS_CHAINS],
    ends: &mut Keccak256,
) -> Option<()> {
    for (chain, &digit) in digits.iter().enumerate() {
        let mut value = B128::new(*reader.take()?);
        for step in digit..CHAIN_END {
            address.set_position(chain as u32, u32::from(step));
            value = address.hash_node(&value.0);
        }
        ends.update(value);
    }
    Some(())
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn recover_chains(
    address: &mut HashContext,
    reader: &mut Reader<'_>,
    digits: &[u8; WOTS_CHAINS],
    ends: &mut Keccak256,
) -> Option<()> {
    use crate::hash::VERIFY_BATCH_WIDTH;

    // Buffer a window of chains so independent steps can be batched and the
    // finished nodes can still be streamed into the hasher in chain order.
    const CHAINS_PER_WINDOW: usize = 16;
    const WINDOW_BYTES: usize = CHAINS_PER_WINDOW * NODE_BYTES;
    const { assert!(WOTS_CHAINS.is_multiple_of(CHAINS_PER_WINDOW)) };

    let mut addresses = core::array::from_fn(|_| address.clone());
    for (window, digits) in digits.as_chunks::<CHAINS_PER_WINDOW>().0.iter().enumerate() {
        let offset = window * CHAINS_PER_WINDOW;
        let mut nodes = reader
            .take::<WINDOW_BYTES>()?
            .as_chunks::<NODE_BYTES>()
            .0
            .first_chunk::<CHAINS_PER_WINDOW>()?
            .map(B128::new);

        for step in 0..CHAIN_END {
            let mut chains = [0; VERIFY_BATCH_WIDTH];
            let mut count = 0;
            for (chain, &digit) in digits.iter().enumerate() {
                if digit > step {
                    continue;
                }
                chains[count] = chain;
                count += 1;
                if count == VERIFY_BATCH_WIDTH {
                    for (address, chain) in addresses.iter_mut().zip(chains) {
                        address.set_position((offset + chain) as u32, u32::from(step));
                    }
                    let next = HashContext::hash_nodes(
                        &mut addresses,
                        chains.map(|chain| &nodes[chain].0),
                    );
                    for (chain, node) in chains.into_iter().zip(next) {
                        nodes[chain] = node;
                    }
                    count = 0;
                }
            }
            for &chain in &chains[..count] {
                address.set_position((offset + chain) as u32, u32::from(step));
                nodes[chain] = address.hash_node(&nodes[chain].0);
            }
        }
        for node in nodes {
            ends.update(node);
        }
    }
    Some(())
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
