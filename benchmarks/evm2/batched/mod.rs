//! Experimental scheduling adapter over the pinned dependency's public internals.
//! Hashing, addresses, message framing and parameters come from that dependency.
//! This is benchmark-only code, not an upstream implementation or production API.

mod fors;
mod trees;
mod wots;

use alloy_primitives::B256;
use lean_sphincs::Signature;
use reference_keccak::{self as hash, Hasher};
use reference_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature, internals::*};

const MAX_BATCH: usize = 64;
const FORS_BYTES: usize = FORS_TREES * (FORS_HEIGHT + 1) * N;

/// Pack equal-sized addressed hashes for the dependency's compiled SIMD backend.
/// Partial groups use its scalar remainder; no dummy inputs count as operations.
fn hash_batch<const LEN: usize>(
    count: usize,
    mut fill: impl FnMut(usize, &mut [u8; LEN]),
    output: &mut [Digest],
) {
    assert_eq!(count, output.len());
    let mut inputs = [[0u8; LEN]; MAX_BATCH];
    let mut digests = [[0u8; 32]; MAX_BATCH];
    for start in (0..count).step_by(MAX_BATCH) {
        let size = (count - start).min(MAX_BATCH);
        for (lane, input) in inputs[..size].iter_mut().enumerate() {
            fill(start + lane, input);
        }
        hash::hash_many(
            inputs[..size].as_flattened(),
            LEN,
            digests[..size].as_flattened_mut(),
        );
        for (out, digest) in output[start..start + size].iter_mut().zip(&digests[..size]) {
            out.copy_from_slice(&digest[..N]);
        }
    }
}

fn image(pk_seed: &PkSeed, address: &Adrs, payload: &[u8], output: &mut [u8]) {
    assert_eq!(output.len(), PREFIX_LEN + payload.len());
    output[..N].copy_from_slice(pk_seed);
    output[N..PREFIX_LEN].copy_from_slice(address.as_bytes());
    output[PREFIX_LEN..].copy_from_slice(payload);
}

fn expand(seed: &B256) -> (PkSeed, [u8; 32]) {
    let mut prefix = Hasher::new();
    prefix.update(b"leanSPHINCS").update(&seed.0);
    (
        hash::truncate(prefix.clone().update(&[0]).finalize()),
        prefix.update(&[1]).finalize(),
    )
}

fn public_key(pk_seed: PkSeed, root: Digest) -> B256 {
    let mut bytes = [0; 32];
    bytes[..N].copy_from_slice(&pk_seed);
    bytes[N..].copy_from_slice(&root);
    B256::new(bytes)
}

pub fn key_gen(seed: &B256) -> B256 {
    let (pk_seed, _) = expand(seed);
    let tree = trees::xmss(&pk_seed, seed, &OtsKey::of_index(LAYERS - 1, 0));
    public_key(pk_seed, tree.root())
}

pub fn sign(seed: &B256, message: &B256) -> Signature {
    let (pk_seed, sk_prf) = expand(seed);
    let top = trees::xmss(&pk_seed, seed, &OtsKey::of_index(LAYERS - 1, 0));
    let randomizer = prf_msg(&sk_prf, &pk_seed, &message.0);
    let (index, leaves) = digest_fields(&h_msg(&randomizer, &pk_seed, &top.root(), &message.0));
    let mut output = Signature::ZERO;
    output[..N].copy_from_slice(&randomizer);
    let mut signed = fors::open(
        &pk_seed,
        seed,
        index,
        &leaves,
        &mut output[N..N + FORS_BYTES],
    );
    let mut offset = N + FORS_BYTES;
    for (layer, height) in LAYER_HEIGHTS.into_iter().enumerate() {
        let key = OtsKey::of_index(layer, index);
        let (counter, chains) = wots::sign(&pk_seed, seed, &key, &signed);
        output[offset..offset + COUNTER_LEN].copy_from_slice(&counter.to_be_bytes());
        offset += COUNTER_LEN;
        output[offset..offset + V * N].copy_from_slice(chains.as_flattened());
        offset += V * N;
        let lower;
        let tree = if layer == LAYERS - 1 {
            &top
        } else {
            lower = trees::xmss(&pk_seed, seed, &key);
            &lower
        };
        for z in 0..height {
            output[offset..offset + N]
                .copy_from_slice(&tree.levels[z][(key.leaf as usize >> z) ^ 1]);
            offset += N;
        }
        signed = tree.root();
    }
    assert_eq!(offset, output.len());
    output
}

pub fn verify(key: &B256, message: &B256, signature: &[u8]) -> bool {
    let Ok(bytes) = <&[u8; reference_sphincs::SIG_SIZE]>::try_from(signature) else {
        return false;
    };
    // Reuse the dependency's wire decoders for the fields consumed below.
    let pk = LeanSphincsPublicKey::from_bytes(&key.0);
    let parsed = LeanSphincsSignature::from_bytes(bytes);
    let pk_seed = pk_seed(&pk);
    let (index, leaves) = digest_fields(&h_msg(
        sig_randomizer(&parsed),
        pk_seed,
        pk_root(&pk),
        &message.0,
    ));
    let mut signed = fors::recover(pk_seed, index, &leaves, &signature[N..N + FORS_BYTES]);
    for (layer, signature) in sig_layers(&parsed).iter().enumerate() {
        let key = OtsKey::of_index(layer, index);
        let Some(leaf) = wots::recover(
            pk_seed,
            &key,
            &signed,
            signature.counter(),
            signature.wots(),
        ) else {
            return false;
        };
        signed = tree_fold(pk_seed, &key, leaf, sig_path(&parsed, layer), |_| ());
    }
    signed == *pk_root(&pk)
}
