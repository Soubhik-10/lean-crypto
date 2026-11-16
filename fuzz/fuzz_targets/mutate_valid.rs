#![no_main]
use libfuzzer_sys::fuzz_target;
fuzz_target!(|data: &[u8]| {
    lean_sphincs_testing::check_mutated_fixture(data).unwrap();
});
