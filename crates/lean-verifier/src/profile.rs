//! Fixed program identity of the pinned aggregation guest.

/// Reference revision whose program, transcript, encoding and security parameters are supported.
pub const REFERENCE_REVISION: &str = "84780fb42667bc288c0e567c125b7e10479fb568";

/// Number of u64 words in the pinned stacked aggregation bytecode.
pub const PROGRAM_WORDS: usize = 8_388_608;

/// Number of coordinates in the aggregate's deferred bytecode evaluation point.
pub const BYTECODE_VARIABLES: usize = 23;

/// Keccak-256 of the reference protocol tag followed by the little-endian program words.
pub const PROGRAM_IV: [u8; 32] = [
    159, 209, 252, 214, 170, 205, 237, 196, 150, 82, 203, 71, 23, 182, 180, 139, 60, 76, 53, 203,
    186, 122, 7, 11, 63, 208, 116, 149, 201, 189, 245, 75,
];
