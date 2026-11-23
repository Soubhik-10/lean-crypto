//! leanSPHINCS aggregation with Alloy keys and messages, using the pinned leanVM backend.
//!
//! Call [`setup`] once before proving. [`Aggregator`] verifies fresh signatures with
//! `lean-sphincs`, then passes their unchanged encoding to the reference prover.
//! Children are verified when decoded by [`Aggregate::from_bytes`] and moved into
//! an aggregator without copying their proof buffers. Locally generated aggregates
//! can be passed directly to their parent.
//!
//! Proof bytes, statement construction, recursion and deferred bytecode verification
//! are the reference implementation's. This crate supports only leanSPHINCS claims;
//! the reference's leanXMSS list is empty and its DA commitment is absent.
//!
//! The default is the reference stable prover. `experimental-prover` selects its
//! experimental prover, using the same protocol. `asm-keccak` accelerates native
//! signature admission through `lean-sphincs`; it does not change the proof backend.
//!
//! Proving is blocking and uses substantial memory. Callers must bound untrusted
//! signature counts and proof byte lengths before admission or decoding. This crate
//! does not define transaction policy, dependency digests or a consensus profile.

#![forbid(unsafe_code)]

mod aggregate;
mod claims;
mod prover;

pub use aggregate::Aggregate;
pub use claims::Claims;
pub use lean_sphincs::B256;
pub use lean_vm::{AggregateError, MAX_LOG_INV_RATE, MAX_RECURSIONS, MIN_LOG_INV_RATE, setup};
pub use prover::Aggregator;
