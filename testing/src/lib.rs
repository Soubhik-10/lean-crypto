//! Shared differential oracles for randomized campaigns and coverage-guided fuzzing.
#![forbid(unsafe_code)]
mod build_info;
mod cases;
mod fixtures;
mod mutations;
mod oracle;

#[cfg(feature = "aggregate")]
pub mod aggregate;

pub use build_info::build_metadata;
pub use cases::{Case, CaseStats, check_case, generated_case};
pub use fixtures::{Fixture, fixtures};
pub use mutations::{check_mutated_fixture, check_wire};
pub use oracle::{Failure, check_verification, reference_verify};

/// Exact comparison revision; keep synchronized with Cargo.toml.
pub const REFERENCE_REVISION: &str = "f7ba4999ae523b94c8d0969b32762c3effea4cbd";

/// Hashing backend selected for the implementation under test.
pub const fn backend() -> &'static str {
    if cfg!(feature = "asm-keccak") {
        "asm-keccak"
    } else if cfg!(feature = "tiny-keccak") {
        "tiny-keccak"
    } else {
        "RustCrypto"
    }
}
