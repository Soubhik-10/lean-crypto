//! Public failure categories for profile preparation, decoding and verification.

use core::fmt;

/// Why the requested aggregate could not be verified.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// Program length, encoding or cryptographic fingerprint differs from the pinned program.
    Program,
    /// Bytes are not exactly one canonically encoded aggregate proof.
    Encoding,
    /// A signature claim list is unsorted or contains duplicate pairs.
    Claims,
    /// The complete proof, expected statement or deferred bytecode check failed.
    Proof,
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Program => "unsupported aggregation program",
            Self::Encoding => "invalid aggregate proof encoding",
            Self::Claims => "signature claims are not strictly sorted",
            Self::Proof => "aggregate proof does not verify",
        })
    }
}

impl core::error::Error for VerifyError {}
