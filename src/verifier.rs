//! Wire-oriented verification, following EthLib's `Verify`, `Address`, `Fors`,
//! `Ots`, `Digest` and `Serialization` specifications at the revision in lib.rs.

use alloy_primitives::{B128, B256, Keccak256, keccak256};

const NODE_BYTES: usize = 16;
const PREFIX_BYTES: usize = 48;
const FORS_TREES: usize = 24;
const FORS_HEIGHT: u32 = 10;
const WOTS_CHAINS: usize = 64;
const CHAIN_END: u8 = 3;
const TARGET_SUM: u16 = 128;
const LAYER_HEIGHTS: [u32; 3] = [8, 8, 10];

// FIPS 205 address type codes, plus leanSPHINCS's WOTS+C encoding domain.
const WOTS_CHAIN: u32 = 0;
const WOTS_PUBLIC_KEY: u32 = 1;
const HYPERTREE: u32 = 2;
const FORS_TREE: u32 = 3;
const FORS_PUBLIC_KEY: u32 = 4;
const WOTS_ENCODING: u32 = 7;

// Every tweakable hash begins with PK.seed and FIPS 205's 32-byte address.
// Keeping the encoded prefix lets short hashes use one contiguous input.
struct Address([u8; PREFIX_BYTES]);

impl Address {
    fn new(public_key: &B256) -> Self {
        let mut prefix = [0; PREFIX_BYTES];
        prefix[..NODE_BYTES].copy_from_slice(&public_key[..NODE_BYTES]);
        Self(prefix)
    }

    fn set_tree(&mut self, layer: u32, tree: u64) {
        self.0[16..20].copy_from_slice(&layer.to_be_bytes());
        // The high 32 bits of the 96-bit tree address stay zero.
        self.0[24..32].copy_from_slice(&tree.to_be_bytes());
    }

    fn set_domain(&mut self, domain: u32, key_pair: u32) {
        self.0[32..36].copy_from_slice(&domain.to_be_bytes());
        self.0[36..40].copy_from_slice(&key_pair.to_be_bytes());
        self.0[40..].fill(0);
    }

    fn set_position(&mut self, height_or_chain: u32, index_or_step: u32) {
        self.0[40..44].copy_from_slice(&height_or_chain.to_be_bytes());
        self.0[44..48].copy_from_slice(&index_or_step.to_be_bytes());
    }

    fn hash_node(&self, value: &[u8; NODE_BYTES]) -> B128 {
        let mut input = [0; PREFIX_BYTES + NODE_BYTES];
        input[..PREFIX_BYTES].copy_from_slice(&self.0);
        input[PREFIX_BYTES..].copy_from_slice(value);
        truncate(keccak256(input))
    }

    fn hash_parent(&self, value: &B128, sibling: &[u8; NODE_BYTES], right: bool) -> B128 {
        let mut input = [0; PREFIX_BYTES + 2 * NODE_BYTES];
        input[..PREFIX_BYTES].copy_from_slice(&self.0);
        let (left, right) = if right {
            (sibling, &value.0)
        } else {
            (&value.0, sibling)
        };
        input[PREFIX_BYTES..PREFIX_BYTES + NODE_BYTES].copy_from_slice(left);
        input[PREFIX_BYTES + NODE_BYTES..].copy_from_slice(right);
        truncate(keccak256(input))
    }

    fn encode(&self, message: &B128, counter: &[u8; 4]) -> B128 {
        let mut input = [0; PREFIX_BYTES + NODE_BYTES + 4];
        input[..PREFIX_BYTES].copy_from_slice(&self.0);
        input[PREFIX_BYTES..PREFIX_BYTES + NODE_BYTES].copy_from_slice(message.as_slice());
        input[PREFIX_BYTES + NODE_BYTES..].copy_from_slice(counter);
        truncate(keccak256(input))
    }

    fn accumulator(&self) -> Keccak256 {
        let mut hasher = Keccak256::new();
        hasher.update(self.0);
        hasher
    }
}

// Reads only fixed-size fields, without materializing a 7.7 KB signature struct.
struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    fn take<const N: usize>(&mut self) -> Option<&'a [u8; N]> {
        let (field, remaining) = self.0.split_first_chunk::<N>()?;
        self.0 = remaining;
        Some(field)
    }
}

pub(super) fn recover_root(public_key: &B256, message: &B256, signature: &[u8]) -> Option<B128> {
    let mut reader = Reader(signature);
    let digest = message_digest(public_key, message, reader.take()?);
    // FIPS 205 Algorithm 19: 30 FORS bytes, an 18-bit tree, then an 8-bit leaf.
    // The six unused high bits of byte 30 are deliberately discarded.
    let tree = u32::from_be_bytes([0, digest[30], digest[31], digest[32]]) & ((1 << 18) - 1);
    let mut index = u64::from((tree << 8) | u32::from(digest[33]));
    let mut address = Address::new(public_key);
    address.set_tree(0, u64::from(tree));
    let mut node = recover_fors(&mut address, &mut reader, &digest, u32::from(digest[33]))?;

    for (layer, height) in LAYER_HEIGHTS.into_iter().enumerate() {
        let leaf = (index & ((1 << height) - 1)) as u32;
        index >>= height;
        address.set_tree(layer as u32, index);
        node = recover_wots(&mut address, &mut reader, leaf, node)?;
        address.set_domain(HYPERTREE, 0);
        node = climb(&mut address, &mut reader, leaf, height, node)?;
    }
    reader.0.is_empty().then_some(node)
}

fn truncate(hash: B256) -> B128 {
    let mut node = [0; NODE_BYTES];
    node.copy_from_slice(&hash[..NODE_BYTES]);
    B128::new(node)
}

fn message_digest(public_key: &B256, message: &B256, randomizer: &[u8; NODE_BYTES]) -> [u8; 34] {
    let mut input = [0; 84];
    input[..16].copy_from_slice(randomizer);
    input[16..48].copy_from_slice(public_key.as_slice());
    input[48..80].copy_from_slice(message.as_slice());
    let first = keccak256(input);
    input[83] = 1;
    let second = keccak256(input);
    let mut digest = [0; 34];
    digest[..32].copy_from_slice(first.as_slice());
    digest[32..].copy_from_slice(&second[..2]);
    digest
}

fn recover_fors(
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

fn recover_wots(
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

fn climb(
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
