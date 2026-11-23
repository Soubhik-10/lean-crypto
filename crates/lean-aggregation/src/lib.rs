//! Canonical leanSPHINCS claims and optional aggregation with the pinned leanVM backend.
//!
//! [`Claims`] and [`B256`] are available with `no_std` and `alloc` when default
//! features are disabled. This mode requires Rust 1.90 and does not build leanVM.
//! The default `std` feature enables proof generation and verification, which
//! require Rust 1.97.1 for the reference backend. `experimental-prover` also
//! enables `std` and selects the reference experimental prover.
//!
//! With `std`, call `setup` once before proving. `Aggregator` verifies fresh
//! signatures with `lean-sphincs`, then passes their unchanged encoding to the
//! reference prover. Received children are fully verified by
//! `Aggregate::from_bytes` and moved into an aggregator without copying proof
//! buffers. Locally generated aggregates can be passed directly to their parent.
//!
//! Proof bytes, statement construction, recursion and deferred bytecode verification
//! are the reference implementation's. This crate supports only leanSPHINCS claims;
//! the reference's leanXMSS list is empty and its DA commitment is absent.
//! `asm-keccak` accelerates native signature admission through `lean-sphincs`;
//! it does not change the proof backend.
//!
//! Proving is blocking and uses substantial memory. Callers must bound untrusted
//! signature counts and proof byte lengths before admission or decoding. This crate
//! does not define transaction policy, dependency digests or a consensus profile.

#![cfg_attr(not(feature = "std"), no_std)]
#![forbid(unsafe_code)]

extern crate alloc;

mod claims;

#[cfg(feature = "std")]
mod aggregate;
#[cfg(feature = "std")]
mod prover;

pub use claims::Claims;
pub use lean_sphincs::B256;

#[cfg(feature = "std")]
pub use aggregate::Aggregate;
#[cfg(feature = "std")]
pub use lean_vm::{AggregateError, MAX_LOG_INV_RATE, MAX_RECURSIONS, MIN_LOG_INV_RATE, setup};
#[cfg(feature = "std")]
pub use prover::Aggregator;
