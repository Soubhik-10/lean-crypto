#![no_main]
use lean_sphincs_testing::{Case, check_case};
use libfuzzer_sys::fuzz_target;
fuzz_target!(|data: &[u8]| {
    let mut bytes = [0; 64];
    let length = data.len().min(bytes.len());
    bytes[..length].copy_from_slice(&data[..length]);
    let input = Case {
        secret_seed: bytes[..32].try_into().unwrap(),
        message: bytes[32..].try_into().unwrap(),
    };
    let index = u64::from_le_bytes(bytes[..8].try_into().unwrap());
    check_case(&input, index).unwrap();
});
