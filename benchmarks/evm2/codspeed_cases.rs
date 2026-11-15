use super::fixtures;
use divan::{Bencher, black_box};

#[divan::bench(args = [0, 1, 2])]
fn verify(bencher: Bencher, index: usize) {
    let case = &fixtures().cases[index];
    bencher.bench(|| {
        lean_sphincs::verify(
            black_box(&case.public_key),
            black_box(&case.message),
            black_box(case.signature.as_slice()),
        )
    });
}

#[divan::bench(args = [0, 1, 2])]
fn sign(bencher: Bencher, index: usize) {
    let case = &fixtures().cases[index];
    bencher.bench(|| lean_sphincs::sign(black_box(&case.seed), black_box(&case.message)));
}

#[divan::bench]
fn key_gen(bencher: Bencher) {
    let case = &fixtures().cases[0];
    bencher.bench(|| lean_sphincs::key_gen(black_box(&case.seed)));
}

#[divan::bench]
fn late_reject(bencher: Bencher) {
    let fixtures = fixtures();
    let case = &fixtures.cases[0];
    bencher.bench(|| {
        lean_sphincs::verify(
            black_box(&case.public_key),
            black_box(&case.message),
            black_box(fixtures.late_reject.as_slice()),
        )
    });
}

#[divan::bench]
fn ecrecover(bencher: Bencher) {
    let fixtures = fixtures();
    let provider = evm2::precompiles::crypto();
    bencher.bench(|| {
        provider.secp256k1_ecrecover(
            black_box(&fixtures.ec_signature),
            black_box(fixtures.ec_recovery_id),
            black_box(&fixtures.ec_message.0),
        )
    });
}

#[divan::bench(args = [64, 80, 1072])]
fn keccak256(bencher: Bencher, bytes: usize) {
    let input = [0x42; 1072];
    bencher.bench(|| alloy_primitives::keccak256(black_box(&input[..bytes])));
}
