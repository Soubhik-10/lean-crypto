#[path = "../../tests/common/mod.rs"]
mod common;

use alloy_primitives::B256;
use evm2::precompiles;
use lean_sphincs::verify;
use secp256k1::{Message, SecretKey, ecdsa::RecoverableSignature};
use serde::Serialize;
use std::{
    env,
    error::Error,
    fs,
    hint::black_box,
    path::PathBuf,
    process::Command,
    time::{Duration, Instant},
};

#[derive(Serialize)]
struct Measurement {
    name: &'static str,
    iterations_per_sample: u64,
    median_ns: f64,
    p05_ns: f64,
    p95_ns: f64,
    samples_ns: Vec<f64>,
}

#[derive(Serialize)]
struct Report {
    cpu: String,
    affinity: Option<String>,
    os: &'static str,
    architecture: &'static str,
    rustc: String,
    evm2_git_source: String,
    alloy_git_source: String,
    ecrecover_backend: &'static str,
    keccak_backend: &'static str,
    sample_ms: u64,
    measurements: Vec<Measurement>,
    verification_to_ecrecover_ratio: f64,
    time_ratio_gas_at_3000: f64,
    time_ratio_frame_gas_at_2800: f64,
    methodology: &'static str,
}

fn measure(
    name: &'static str,
    sample_count: usize,
    sample_time: Duration,
    mut operation: impl FnMut(),
) -> Measurement {
    let mut iterations = 1u64;
    loop {
        let start = Instant::now();
        for _ in 0..iterations {
            operation();
        }
        if start.elapsed() >= sample_time {
            break;
        }
        iterations *= 2;
    }
    let mut samples = Vec::with_capacity(sample_count);
    for _ in 0..sample_count {
        let start = Instant::now();
        for _ in 0..iterations {
            operation();
        }
        samples.push(start.elapsed().as_secs_f64() * 1e9 / iterations as f64);
    }
    let mut ordered = samples.clone();
    ordered.sort_by(f64::total_cmp);
    let median = if sample_count.is_multiple_of(2) {
        (ordered[sample_count / 2 - 1] + ordered[sample_count / 2]) / 2.0
    } else {
        ordered[sample_count / 2]
    };
    Measurement {
        name,
        iterations_per_sample: iterations,
        median_ns: median,
        p05_ns: ordered[((sample_count - 1) as f64 * 0.05).round() as usize],
        p95_ns: ordered[((sample_count - 1) as f64 * 0.95).round() as usize],
        samples_ns: samples,
    }
}

fn command_output(program: &str, args: &[&str]) -> Result<String, Box<dyn Error>> {
    let output = Command::new(program).args(args).output()?;
    if !output.status.success() {
        return Err(format!(
            "{program} {args:?} failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )
        .into());
    }
    Ok(String::from_utf8(output.stdout)?.trim().to_owned())
}

fn git_source(package: &str) -> Result<String, Box<dyn Error>> {
    let name = format!("name = \"{package}\"");
    let block = include_str!("Cargo.lock")
        .split("[[package]]")
        .find(|block| block.lines().any(|line| line == name))
        .ok_or_else(|| format!("{package} missing from benchmark lockfile"))?;
    let source = block
        .lines()
        .find_map(|line| line.strip_prefix("source = \""))
        .and_then(|source| source.strip_suffix('"'))
        .filter(|source| source.starts_with("git+"))
        .ok_or_else(|| format!("{package} is not locked to a Git source"))?;
    Ok(source.to_owned())
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut sample_count = 30usize;
    let mut sample_ms = 100u64;
    let mut json_path = None;
    let mut args = env::args().skip(1);
    while let Some(argument) = args.next() {
        match argument.as_str() {
            "--bench" => {}
            "--samples" => sample_count = args.next().ok_or("missing sample count")?.parse()?,
            "--sample-ms" => sample_ms = args.next().ok_or("missing sample duration")?.parse()?,
            "--json" => json_path = Some(PathBuf::from(args.next().ok_or("missing JSON path")?)),
            _ => return Err(format!("unknown argument: {argument}").into()),
        }
    }
    if !(5..=1000).contains(&sample_count) || !(10..=1000).contains(&sample_ms) {
        return Err("use 5..=1000 samples and 10..=1000 milliseconds per sample".into());
    }

    let valid: Vec<_> = common::vectors()
        .into_iter()
        .filter(|case| case.expected == Some(true))
        .map(|case| case.valid_inputs())
        .collect();
    for (key, message, signature) in &valid {
        assert!(verify(key, message, signature));
    }
    let (key, message, mut late_reject) = common::known_answer();
    *late_reject.last_mut().ok_or("empty fixture")? ^= 1;
    assert!(!verify(&key, &message, &late_reject));

    // Generate outside the timed region. The measured call receives wire-format r/s,
    // exactly as evm2's frame validation does, and also performs address hashing.
    let ec_message = B256::repeat_byte(42);
    let secret = SecretKey::from_secret_bytes([1; 32])?;
    let signed =
        RecoverableSignature::sign_ecdsa_recoverable(Message::from_digest(ec_message.0), &secret);
    let (recovery_id, compact) = signed.serialize_compact();
    let provider = precompiles::crypto();
    let expected = provider.secp256k1_ecrecover(&compact, recovery_id.to_u8(), &ec_message.0)?;
    let public_key = signed.recover_ecdsa(Message::from_digest(ec_message.0))?;
    let mut expected_word = alloy_primitives::keccak256(&public_key.serialize_uncompressed()[1..]);
    expected_word[..12].fill(0);
    assert_eq!(expected, expected_word.0);

    let sample_time = Duration::from_millis(sample_ms);
    let ecrecover = measure("evm2/ecrecover", sample_count, sample_time, || {
        black_box(provider.secp256k1_ecrecover(
            black_box(&compact),
            black_box(recovery_id.to_u8()),
            black_box(&ec_message.0),
        ))
        .expect("valid benchmark signature");
    });
    let mut index = 0usize;
    let verification = measure("lean_sphincs/valid", sample_count, sample_time, || {
        let (key, message, signature) = &valid[index % valid.len()];
        index = index.wrapping_add(1);
        black_box(verify(
            black_box(key),
            black_box(message),
            black_box(signature),
        ));
    });
    let late = measure(
        "lean_sphincs/late_reject",
        sample_count,
        sample_time,
        || {
            black_box(verify(
                black_box(&key),
                black_box(&message),
                black_box(&late_reject),
            ));
        },
    );
    let ratio = verification.median_ns / ecrecover.median_ns;
    let report = Report {
        cpu: env::var("BENCH_CPU")
            .or_else(|_| env::var("PROCESSOR_IDENTIFIER"))
            .unwrap_or_else(|_| "unreported".to_owned()),
        affinity: env::var("BENCH_AFFINITY").ok(),
        os: env::consts::OS,
        architecture: env::consts::ARCH,
        rustc: command_output("rustc", &["--version"])?,
        evm2_git_source: git_source("evm2")?,
        alloy_git_source: git_source("alloy-primitives")?,
        ecrecover_backend: if cfg!(feature = "secp256k1") {
            "evm2 Crypto provider / libsecp256k1"
        } else {
            "evm2 Crypto provider / k256"
        },
        keccak_backend: if cfg!(feature = "asm-keccak") {
            "Alloy asm-keccak"
        } else {
            "Alloy default (RustCrypto sha3)"
        },
        sample_ms,
        measurements: vec![ecrecover, verification, late],
        verification_to_ecrecover_ratio: ratio,
        time_ratio_gas_at_3000: ratio * 3000.0,
        time_ratio_frame_gas_at_2800: ratio * 2800.0,
        methodology: "Single-threaded batches; calibration and fixture setup excluded. Valid verification rotates all three valid EthLib cases. Late rejection changes the last signature byte. Ecrecover calls evm2's actual Crypto provider, including compact-signature parsing, recovery, serialization and address hashing; provider initialization is excluded. Percentiles describe batch-average ns/op, not individual-call latency. Gas numbers are ratios of medians on this machine, not consensus prices or cross-client calibration.",
    };
    println!(
        "CPU: {}\n{}\n{}\n{}",
        report.cpu, report.rustc, report.ecrecover_backend, report.keccak_backend
    );
    for measurement in &report.measurements {
        println!(
            "{}: {:.2} us/op (p05 {:.2}, p95 {:.2}; {} samples)",
            measurement.name,
            measurement.median_ns / 1000.0,
            measurement.p05_ns / 1000.0,
            measurement.p95_ns / 1000.0,
            sample_count
        );
    }
    println!(
        "leanSPHINCS/ecrecover: {ratio:.3}x; time-ratio gas: {:.0} at 3000, {:.0} at 2800",
        report.time_ratio_gas_at_3000, report.time_ratio_frame_gas_at_2800
    );
    if let Some(path) = json_path {
        fs::write(path, serde_json::to_string_pretty(&report)? + "\n")?;
    }
    Ok(())
}
