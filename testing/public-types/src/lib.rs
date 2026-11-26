//! Compile a downstream caller with registry types and no dependency patches.

use alloy_primitives::{B256, FixedBytes};

pub fn public_types(key: B256, message: B256, signature: FixedBytes<7740>) {
    let _: lean_sphincs::B256 = key;
    let _: lean_aggregation::B256 = key;
    let _: lean_verifier::B256 = key;
    let _: lean_sphincs::Signature = signature;
    let _ = lean_sphincs::verify(&key, &message, signature.as_slice());
    let _ = lean_aggregation::Claims::new([(key, message)]);
    let _ = lean_verifier::AggregateClaims {
        lean_sphincs: vec![(key, message)],
        ..Default::default()
    };
}
