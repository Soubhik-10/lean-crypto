//! Keccak hashing and FIPS 205 address encoding.

use alloy_primitives::{B128, B256, Keccak256, keccak256_uncached};

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "sse2",
    not(target_feature = "avx2")
))]
mod pair;

pub(crate) const NODE_BYTES: usize = 16;
const PREFIX_BYTES: usize = 48;
const NODE_INPUT_BYTES: usize = PREFIX_BYTES + NODE_BYTES;
const PARENT_INPUT_BYTES: usize = PREFIX_BYTES + 2 * NODE_BYTES;

// Every tweakable hash begins with PK.seed and FIPS 205's 32-byte address.
// The prefix stays in place between hashes. The tail holds the current payload.
#[derive(Clone)]
pub(crate) struct Address([u8; PARENT_INPUT_BYTES]);

impl Address {
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

    pub(crate) fn accumulator(&self) -> Keccak256 {
        let mut hasher = Keccak256::new();
        hasher.update(&self.0[..PREFIX_BYTES]);
        hasher
    }
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "sse2",
    not(target_feature = "avx2")
))]
impl Address {
    pub(crate) fn hash_node_pair(
        addresses: &mut [Self; 2],
        values: [&[u8; NODE_BYTES]; 2],
    ) -> [B128; 2] {
        let [first, second] = addresses;
        pair::hash(first.node_input(values[0]), second.node_input(values[1]))
    }

    pub(crate) fn hash_parent_pair(
        addresses: &mut [Self; 2],
        values: &[B128; 2],
        siblings: [&[u8; NODE_BYTES]; 2],
        positions: [u32; 2],
    ) -> [B128; 2] {
        let [first, second] = addresses;
        pair::hash(
            first.parent_input(&values[0], siblings[0], positions[0] & 1 != 0),
            second.parent_input(&values[1], siblings[1], positions[1] & 1 != 0),
        )
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
