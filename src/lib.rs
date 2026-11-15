//! Key generation, signing and verification for the leanSPHINCS configuration in EthLib at
//! `03547dd83f298a63e6dcceff0a0b75f6142490aa`.
//!
//! This is the Keccak-256 / WOTS+C / FORS configuration with a three-layer
//! hypertree of heights 8, 8 and 10. It is a variant of SLH-DSA, not a verifier
//! for the standardized FIPS 205 parameter sets.
//!
//! Public keys and message digests are Alloy [`B256`] values. Signatures are
//! borrowed directly from their wire encoding. Verification needs no allocator,
//! signing key, operating system, or VM. Key generation and signing accept a
//! secret seed and also require no allocator. Signing caches approximately 32 KiB
//! of public tree nodes on the stack; verification processes only public values.
//!
//! The protocol and its parameters are still experimental. Passing the reference
//! vectors is not a security audit or a proof of this implementation.

#![no_std]
#![forbid(unsafe_code)]

mod fors;
mod hash;
mod params;
mod signature;
mod signing;
mod tree;
mod verifier;
mod wots;

pub use alloy_primitives::B256;
pub use signing::{SignError, key_gen, sign};

/// Size of a public key, encoded as `PK.seed || PK.root`.
pub const PUBLIC_KEY_BYTES: usize = 32;

/// Size of the message digest accepted by this configuration.
pub const MESSAGE_BYTES: usize = 32;

/// Size of a complete serialized signature.
pub const SIGNATURE_BYTES: usize = 7740;

/// A complete serialized leanSPHINCS signature.
pub type Signature = alloy_primitives::FixedBytes<SIGNATURE_BYTES>;

/// Verifies a signature over a 32-byte message digest.
///
/// `public_key` is `PK.seed || PK.root`, with 16 bytes per component. `message`
/// is the exact digest being signed; this function performs no transaction
/// hashing or domain separation on the caller's behalf.
///
/// Returns `false` for an incorrect signature or any signature length other than
/// [`SIGNATURE_BYTES`]. Public-key and message lengths are enforced by [`B256`].
/// The signature is read in place, and no heap allocation is performed.
pub fn verify(public_key: &B256, message: &B256, signature: &[u8]) -> bool {
    signature.len() == SIGNATURE_BYTES
        && verifier::recover_root(public_key, message, signature)
            .is_some_and(|root| root.as_slice() == &public_key[16..])
}
