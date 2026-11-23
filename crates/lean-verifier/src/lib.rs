//! Independent, reference-derived aggregate-proof verification for leanVM.
//!
//! The verifier uses `no_std` and `alloc`; its only runtime dependency is the
//! workspace's Alloy primitives. The pinned reference is used only in tests.

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

// Keep the reference's numeric indexing and protocol argument lists for review.
#[allow(clippy::needless_range_loop, clippy::too_many_arguments)]
mod vm;

mod claims;
mod error;
mod profile;
mod proof;
mod verifier;

pub use alloy_primitives::B256;
pub use claims::AggregateClaims;
pub use error::VerifyError;
pub use profile::{BYTECODE_VARIABLES, PROGRAM_IV, PROGRAM_WORDS, REFERENCE_REVISION};
pub use proof::AggregateProof;
pub use verifier::Verifier;
