//! Keccak hashing and FIPS 205 address encoding.

use alloy_primitives::{B128, B256, Keccak256, keccak256};

const NODE_BYTES: usize = 16;
const PREFIX_BYTES: usize = 48;

// Every tweakable hash begins with PK.seed and FIPS 205's 32-byte address.
// Keeping the encoded prefix lets short hashes use one contiguous input.
pub(crate) struct Address([u8; PREFIX_BYTES]);

impl Address {
    pub(crate) fn new(public_key: &B256) -> Self {
        let mut prefix = [0; PREFIX_BYTES];
        prefix[..NODE_BYTES].copy_from_slice(&public_key[..NODE_BYTES]);
        Self(prefix)
    }

    pub(crate) fn set_tree(&mut self, layer: u32, tree: u64) {
        self.0[16..20].copy_from_slice(&layer.to_be_bytes());
        // The high 32 bits of the 96-bit tree address stay zero.
        self.0[24..32].copy_from_slice(&tree.to_be_bytes());
    }

    pub(crate) fn set_domain(&mut self, domain: u32, key_pair: u32) {
        self.0[32..36].copy_from_slice(&domain.to_be_bytes());
        self.0[36..40].copy_from_slice(&key_pair.to_be_bytes());
        self.0[40..].fill(0);
    }

    pub(crate) fn set_position(&mut self, height_or_chain: u32, index_or_step: u32) {
        self.0[40..44].copy_from_slice(&height_or_chain.to_be_bytes());
        self.0[44..48].copy_from_slice(&index_or_step.to_be_bytes());
    }

    pub(crate) fn hash_node(&self, value: &[u8; NODE_BYTES]) -> B128 {
        let mut input = [0; PREFIX_BYTES + NODE_BYTES];
        input[..PREFIX_BYTES].copy_from_slice(&self.0);
        input[PREFIX_BYTES..].copy_from_slice(value);
        truncate(keccak256(input))
    }

    pub(crate) fn hash_parent(
        &self,
        value: &B128,
        sibling: &[u8; NODE_BYTES],
        right: bool,
    ) -> B128 {
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

    pub(crate) fn encode(&self, message: &B128, counter: &[u8; 4]) -> B128 {
        let mut input = [0; PREFIX_BYTES + NODE_BYTES + 4];
        input[..PREFIX_BYTES].copy_from_slice(&self.0);
        input[PREFIX_BYTES..PREFIX_BYTES + NODE_BYTES].copy_from_slice(message.as_slice());
        input[PREFIX_BYTES + NODE_BYTES..].copy_from_slice(counter);
        truncate(keccak256(input))
    }

    pub(crate) fn accumulator(&self) -> Keccak256 {
        let mut hasher = Keccak256::new();
        hasher.update(self.0);
        hasher
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
    let first = keccak256(input);
    input[83] = 1;
    let second = keccak256(input);
    let mut digest = [0; 34];
    digest[..32].copy_from_slice(first.as_slice());
    digest[32..].copy_from_slice(&second[..2]);
    digest
}
