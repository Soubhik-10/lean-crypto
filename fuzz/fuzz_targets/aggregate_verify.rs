#![no_main]

use libfuzzer_sys::fuzz_target;
use std::{path::PathBuf, sync::OnceLock};

fuzz_target!(|data: &[u8]| {
    static VERIFIER: OnceLock<lean_sphincs_testing::aggregate::Verifier> = OnceLock::new();
    let verifier = VERIFIER.get_or_init(|| {
        let program = std::env::var_os("LEAN_AGGREGATE_PROGRAM")
            .map(PathBuf::from)
            .unwrap_or_else(|| {
                PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("corpus/aggregate-program.bin")
            });
        lean_sphincs_testing::aggregate::load_verifier(&program)
    });
    lean_sphincs_testing::aggregate::check_verification(data, verifier);
});
