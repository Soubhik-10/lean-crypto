//! Keccak hashing and FIPS 205 address encoding.

use alloy_primitives::{B128, B256, Keccak256, keccak256_uncached};

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
mod batch;

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
pub(crate) use batch::WIDTH as VERIFY_BATCH_WIDTH;

use crate::params::NODE_BYTES;
const PREFIX_BYTES: usize = 48;
const NODE_INPUT_BYTES: usize = PREFIX_BYTES + NODE_BYTES;
const PARENT_INPUT_BYTES: usize = PREFIX_BYTES + 2 * NODE_BYTES;

// Every tweakable hash begins with PK.seed and FIPS 205's 32-byte address.
// The prefix stays in place between hashes. The tail holds the current payload.
#[derive(Clone)]
pub(crate) struct HashContext([u8; PARENT_INPUT_BYTES]);

impl HashContext {
    pub(crate) fn new(public_key: &B256) -> Self {
        let mut input = [0; PARENT_INPUT_BYTES];
        input[..NODE_BYTES].copy_from_slice(&public_key[..NODE_BYTES]);
        Self(input)
    }

    pub(crate) fn set_tree(&mut self, layer: u32, tree: u64) {
        self.0[16..20].copy_from_slice(&layer.to_be_bytes());
        // The high 32 bits of the 96-bit tree address stay zero.
        self.0[24..32].copy_from_slice(&tree.to_be_bytes());
    }

    pub(crate) fn set_domain(&mut self, domain: u32, key_pair: u32) {
        self.0[32..36].copy_from_slice(&domain.to_be_bytes());
        self.0[36..40].copy_from_slice(&key_pair.to_be_bytes());
        self.0[40..PREFIX_BYTES].fill(0);
    }

    pub(crate) fn set_position(&mut self, height_or_chain: u32, index_or_step: u32) {
        self.0[40..44].copy_from_slice(&height_or_chain.to_be_bytes());
        self.0[44..48].copy_from_slice(&index_or_step.to_be_bytes());
    }

    fn node_input(&mut self, value: &[u8; NODE_BYTES]) -> &[u8; NODE_INPUT_BYTES] {
        self.0[PREFIX_BYTES..NODE_INPUT_BYTES].copy_from_slice(value);
        self.0.first_chunk().expect("node preimage fits")
    }

    fn parent_input(
        &mut self,
        value: &B128,
        sibling: &[u8; NODE_BYTES],
        right: bool,
    ) -> &[u8; PARENT_INPUT_BYTES] {
        let (left, right) = if right {
            (sibling, &value.0)
        } else {
            (&value.0, sibling)
        };
        self.0[PREFIX_BYTES..NODE_INPUT_BYTES].copy_from_slice(left);
        self.0[NODE_INPUT_BYTES..].copy_from_slice(right);
        &self.0
    }

    pub(crate) fn hash_node(&mut self, value: &[u8; NODE_BYTES]) -> B128 {
        truncate(keccak256_uncached(self.node_input(value)))
    }

    pub(crate) fn hash_parent(
        &mut self,
        value: &B128,
        sibling: &[u8; NODE_BYTES],
        right: bool,
    ) -> B128 {
        truncate(keccak256_uncached(self.parent_input(value, sibling, right)))
    }

    pub(crate) fn encode(&mut self, message: &B128, counter: &[u8; 4]) -> B128 {
        const ENCODE_INPUT_BYTES: usize = NODE_INPUT_BYTES + 4;
        self.0[PREFIX_BYTES..NODE_INPUT_BYTES].copy_from_slice(message.as_slice());
        self.0[NODE_INPUT_BYTES..ENCODE_INPUT_BYTES].copy_from_slice(counter);
        truncate(keccak256_uncached(&self.0[..ENCODE_INPUT_BYTES]))
    }

    pub(crate) fn derive_secret(&mut self, seed: &B256) -> B128 {
        self.0[PREFIX_BYTES..].copy_from_slice(seed.as_slice());
        truncate(keccak256_uncached(self.0))
    }

    pub(crate) fn accumulator(&self) -> Keccak256 {
        let mut hasher = Keccak256::new();
        hasher.update(&self.0[..PREFIX_BYTES]);
        hasher
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
impl HashContext {
    pub(crate) fn set_positions(
        addresses: &mut [Self; VERIFY_BATCH_WIDTH],
        height: u32,
        positions: [u32; VERIFY_BATCH_WIDTH],
    ) {
        let mut lane = 0;
        while lane < VERIFY_BATCH_WIDTH {
            addresses[lane].set_position(height, positions[lane]);
            lane += 1;
        }
    }

    pub(crate) fn hash_nodes(
        addresses: &mut [Self; VERIFY_BATCH_WIDTH],
        values: [B128; VERIFY_BATCH_WIDTH],
    ) -> [B128; VERIFY_BATCH_WIDTH] {
        let mut inputs = [[0; NODE_INPUT_BYTES]; VERIFY_BATCH_WIDTH];
        let mut lane = 0;
        while lane < VERIFY_BATCH_WIDTH {
            inputs[lane] = *addresses[lane].node_input(&values[lane].0);
            lane += 1;
        }
        batch::hash(inputs)
    }

    pub(crate) fn hash_parents(
        addresses: &mut [Self; VERIFY_BATCH_WIDTH],
        values: &[B128; VERIFY_BATCH_WIDTH],
        siblings: [B128; VERIFY_BATCH_WIDTH],
        positions: [u32; VERIFY_BATCH_WIDTH],
    ) -> [B128; VERIFY_BATCH_WIDTH] {
        let mut inputs = [[0; PARENT_INPUT_BYTES]; VERIFY_BATCH_WIDTH];
        let mut lane = 0;
        while lane < VERIFY_BATCH_WIDTH {
            inputs[lane] = *addresses[lane].parent_input(
                &values[lane],
                &siblings[lane].0,
                positions[lane] & 1 != 0,
            );
            lane += 1;
        }
        batch::hash(inputs)
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
pub(crate) fn append_nodes<const N: usize>(hasher: &mut Keccak256, nodes: &[B128; N]) {
    let mut i = 0;
    while i < N {
        hasher.update(nodes[i]);
        i += 1;
    }
}

pub(crate) fn truncate(hash: B256) -> B128 {
    let mut node = [0; NODE_BYTES];
    node.copy_from_slice(&hash[..NODE_BYTES]);
    B128::new(node)
}

pub(crate) fn message_digest(
    public_key: &B256,
    message: &B256,
    randomizer: &[u8; NODE_BYTES],
) -> [u8; 34] {
    let mut input = [0; 84];
    input[..16].copy_from_slice(randomizer);
    input[16..48].copy_from_slice(public_key.as_slice());
    input[48..80].copy_from_slice(message.as_slice());
    let first = keccak256_uncached(input);
    input[83] = 1;
    let second = keccak256_uncached(input);
    let mut digest = [0; 34];
    digest[..32].copy_from_slice(first.as_slice());
    digest[32..].copy_from_slice(&second[..2]);
    digest
}
