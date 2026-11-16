//! Isolates Keccak permutation code generation from signature processing.
use std::{
    hint::black_box,
    io::{self, BufRead},
    time::{Duration, Instant},
};
use tiny_keccak::{Hasher, Keccak, keccakf};

#[inline(never)]
fn hash(input: &[u8]) -> [u8; 32] {
    let mut state = Keccak::v256();
    state.update(input);
    let mut output = [0; 32];
    state.finalize(&mut output);
    output
}

fn measure(mut call: impl FnMut()) -> (f64, u64) {
    let mut iterations = 1u64;
    loop {
        let start = Instant::now();
        for _ in 0..iterations {
            call();
        }
        if start.elapsed() >= Duration::from_millis(10) {
            break;
        }
        iterations *= 2;
    }
    let mut samples = [0f64; 30];
    for sample in &mut samples {
        let start = Instant::now();
        for _ in 0..iterations {
            call();
        }
        *sample = start.elapsed().as_nanos() as f64 / iterations as f64;
    }
    samples.sort_by(f64::total_cmp);
    ((samples[14] + samples[15]) * 0.5, iterations)
}

fn main() {
    if !std::env::args().any(|arg| arg == "--run") {
        return;
    }
    if std::env::args().any(|arg| arg == "--wait-for-start") {
        let mut line = String::new();
        io::stdin().lock().read_line(&mut line).unwrap();
        assert_eq!(line.trim(), "start");
    }
    let empty = hash(&[]);
    assert_eq!(
        empty,
        [
            0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7,
            0x03, 0xc0, 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b, 0x7b, 0xfa, 0xd8, 0x04,
            0x5d, 0x85, 0xa4, 0x70
        ]
    );
    let mut permutation = [0u64; 25];
    let (ns, iterations) = measure(|| {
        keccakf(black_box(&mut permutation));
        black_box(&permutation);
    });
    println!("{{\"case\":\"permutation\",\"median_ns\":{ns},\"iterations\":{iterations}}}");
    for size in [64, 80, 84, 136, 137, 432, 1072, 4096] {
        let input: Vec<u8> = (0..size)
            .map(|i| (i as u8).wrapping_mul(37).wrapping_add(11))
            .collect();
        let expected = hash(&input);
        let (ns, iterations) = measure(|| {
            black_box(hash(black_box(&input)));
        });
        let digest: String = expected.iter().map(|x| format!("{x:02x}")).collect();
        println!(
            "{{\"case\":\"hash/{size}\",\"median_ns\":{ns},\"iterations\":{iterations},\"digest\":\"{digest}\"}}"
        );
    }
}
