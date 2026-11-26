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

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
const CHAINS_PER_WINDOW: usize = 16;

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
    let mut chain = 0;
    while chain < WOTS_CHAINS {
        let value = B128::new(*reader.take()?);
        let value = walk_chain(address, chain as u32, digits[chain], CHAIN_END, value);
        ends.update(value);
        chain += 1;
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
    const { assert!(WOTS_CHAINS.is_multiple_of(CHAINS_PER_WINDOW)) };
    let mut addresses = core::array::from_fn(|_| address.clone());
    let mut window = 0;
    while window < WOTS_CHAINS / CHAINS_PER_WINDOW {
        let offset = window * CHAINS_PER_WINDOW;
        let nodes = read_window(reader)?;
        let nodes = recover_window(address, &mut addresses, digits, offset, nodes);
        crate::hash::append_nodes(ends, &nodes);
        window += 1;
    }
    Some(())
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn read_window(reader: &mut Reader<'_>) -> Option<[B128; CHAINS_PER_WINDOW]> {
    const WINDOW_BYTES: usize = CHAINS_PER_WINDOW * NODE_BYTES;
    let input = reader
        .take::<WINDOW_BYTES>()?
        .as_chunks::<NODE_BYTES>()
        .0
        .first_chunk::<CHAINS_PER_WINDOW>()?;
    Some(core::array::from_fn(|i| B128::new(input[i])))
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn recover_window(
    address: &mut HashContext,
    addresses: &mut [HashContext; crate::hash::VERIFY_BATCH_WIDTH],
    digits: &[u8; WOTS_CHAINS],
    offset: usize,
    mut nodes: [B128; CHAINS_PER_WINDOW],
) -> [B128; CHAINS_PER_WINDOW] {
    use crate::hash::VERIFY_BATCH_WIDTH;
    let mut step = 0;
    while step < CHAIN_END {
        let mut chains = [0; VERIFY_BATCH_WIDTH];
        let mut count = 0;
        let mut chain = 0;
        while chain < CHAINS_PER_WINDOW {
            if digits[offset + chain] <= step {
                chains[count] = chain;
                count += 1;
                if count == VERIFY_BATCH_WIDTH {
                    recover_group(addresses, &mut nodes, chains, offset, step);
                    count = 0;
                }
            }
            chain += 1;
        }
        let mut tail = 0;
        while tail < count {
            let chain = chains[tail];
            address.set_position((offset + chain) as u32, u32::from(step));
            nodes[chain] = address.hash_node(&nodes[chain].0);
            tail += 1;
        }
        step += 1;
    }
    nodes
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn recover_group(
    addresses: &mut [HashContext; crate::hash::VERIFY_BATCH_WIDTH],
    nodes: &mut [B128; CHAINS_PER_WINDOW],
    chains: [usize; crate::hash::VERIFY_BATCH_WIDTH],
    offset: usize,
    step: u8,
) {
    let mut lane = 0;
    while lane < crate::hash::VERIFY_BATCH_WIDTH {
        addresses[lane].set_position((offset + chains[lane]) as u32, u32::from(step));
        lane += 1;
    }
    let values = core::array::from_fn(|lane| nodes[chains[lane]]);
    let next = HashContext::hash_nodes(addresses, values);
    let mut lane = 0;
    while lane < crate::hash::VERIFY_BATCH_WIDTH {
        nodes[chains[lane]] = next[lane];
        lane += 1;
    }
}

fn codeword(code: &B128) -> Option<[u8; WOTS_CHAINS]> {
    let digits = core::array::from_fn(|i| (code[i / 4] >> (6 - 2 * (i % 4))) & 3);
    let mut sum = 0u16;
    let mut i = 0;
    while i < WOTS_CHAINS {
        sum += u16::from(digits[i]);
        i += 1;
    }
    if sum == TARGET_SUM {
        Some(digits)
    } else {
        None
    }
}

fn walk_chain(address: &mut HashContext, chain: u32, start: u8, end: u8, mut node: B128) -> B128 {
    let mut step = start;
    while step < end {
        address.set_position(chain, u32::from(step));
        node = address.hash_node(&node.0);
        step += 1;
    }
    node
}

fn find_encoding(
    address: &mut HashContext,
    message: &B128,
    counter_limit: u64,
) -> Option<(u32, [u8; WOTS_CHAINS])> {
    let mut counter = 0u64;
    while counter < counter_limit {
        if let Some(digits) = codeword(&address.encode(message, &(counter as u32).to_be_bytes())) {
            return Some((counter as u32, digits));
        }
        counter += 1;
    }
    None
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
    let mut chain = 0;
    while chain < WOTS_CHAINS {
        let node = chain_start(address, seed, key_pair, chain as u32);
        let node = walk_chain(address, chain as u32, 0, CHAIN_END, node);
        ends.update(node);
        chain += 1;
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
    let (counter, digits) = find_encoding(address, message, counter_limit)?;
    output[..4].copy_from_slice(&counter.to_be_bytes());
    let mut chain = 0;
    while chain < WOTS_CHAINS {
        let node = chain_start(address, seed, key_pair, chain as u32);
        let node = walk_chain(address, chain as u32, 0, digits[chain], node);
        output[4 + chain * NODE_BYTES..4 + (chain + 1) * NODE_BYTES]
            .copy_from_slice(node.as_slice());
        chain += 1;
    }
    Some(())
}

#[cfg(all(test, target_arch = "x86_64", target_feature = "sse2"))]
#[path = "formal_tests.rs"]
mod formal;
