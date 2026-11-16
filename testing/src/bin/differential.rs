use alloy_primitives::hex;
use lean_sphincs_testing::{
    Case, CaseStats, Failure, REFERENCE_REVISION, backend, check_case, generated_case,
};
use serde_json::json;
use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    sync::{
        Arc,
        atomic::{AtomicBool, AtomicU64, Ordering},
        mpsc,
    },
    thread,
    time::{Instant, SystemTime, UNIX_EPOCH},
};

type Error = Box<dyn std::error::Error>;

struct Options {
    seed: [u8; 32],
    start: u64,
    cases: u64,
    jobs: usize,
    out: PathBuf,
}

fn parse() -> Result<Option<Options>, Error> {
    let mut args = env::args().skip(1);
    let mut seed = None;
    let mut start = 0u64;
    let mut cases = 10_000u64;
    let mut jobs = thread::available_parallelism()
        .map_or(1, usize::from)
        .min(16);
    let mut out = None;
    while let Some(arg) = args.next() {
        let mut value = || {
            args.next()
                .ok_or_else(|| format!("missing value for {arg}"))
        };
        match arg.as_str() {
            "--seed" => {
                let value = value()?;
                let bytes = hex::decode(value.strip_prefix("0x").unwrap_or(&value))?;
                seed = Some(bytes.try_into().map_err(|_| "seed must be 32 bytes")?);
            }
            "--start" => start = value()?.parse()?,
            "--cases" => cases = value()?.parse()?,
            "--jobs" => jobs = value()?.parse()?,
            "--out" => out = Some(PathBuf::from(value()?)),
            "--help" | "-h" => {
                println!(
                    "differential [--cases 10000] [--jobs N] [--seed 64_HEX_DIGITS] [--start INDEX] [--out DIRECTORY]\nEach index deterministically selects an independent ChaCha20 stream. Replay a failure with its recorded seed, index, --cases 1 and --jobs 1."
                );
                return Ok(None);
            }
            _ => return Err(format!("unknown argument {arg}").into()),
        }
    }
    if cases == 0 || cases > 100_000_000 || jobs == 0 || jobs > 256 {
        return Err("need 1..100000000 cases and 1..256 jobs".into());
    }
    start.checked_add(cases).ok_or("case range overflows u64")?;
    let seed = if let Some(seed) = seed {
        seed
    } else {
        let mut seed = [0; 32];
        getrandom::fill(&mut seed).map_err(|e| e.to_string())?;
        seed
    };
    let stamp = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
    let out = out.unwrap_or_else(|| {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("results")
            .join(format!("{stamp}-{}", &hex::encode(seed)[..8]))
    });
    if out.join("run.json").exists() {
        return Err("output already contains a run; use another --out directory".into());
    }
    Ok(Some(Options {
        seed,
        start,
        cases,
        jobs,
        out,
    }))
}

fn command(program: &str, args: &[&str], cwd: &Path) -> Option<String> {
    let output = Command::new(program)
        .args(args)
        .current_dir(cwd)
        .output()
        .ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn write_json(path: &Path, value: &serde_json::Value) -> Result<(), Error> {
    let temporary = path.with_extension("json.tmp");
    fs::write(&temporary, serde_json::to_vec_pretty(value)?)?;
    fs::rename(temporary, path)?;
    Ok(())
}

struct Event {
    index: u64,
    input: Case,
    outcome: Result<CaseStats, Failure>,
}

fn run(options: Options) -> Result<(), Error> {
    fs::create_dir_all(&options.out)?;
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let mut record = json!({
        "schema_version": 1, "status": "running", "master_seed": hex::encode(options.seed),
        "start": options.start, "requested_cases": options.cases, "jobs": options.jobs,
        "generator": "ChaCha20; 32-byte master seed; stream = case index; first 32 bytes secret seed, next 32 message",
        "backend": backend(), "reference_revision": REFERENCE_REVISION,
        "architecture": env::consts::ARCH, "os": env::consts::OS,
        "compiled_avx2": cfg!(target_feature = "avx2"), "compiled_avx512f": cfg!(target_feature = "avx512f"),
        "git_revision": command("git", &["rev-parse", "HEAD"], root),
        "git_status": command("git", &["status", "--porcelain"], root),
        "rustc_at_run": command("rustc", &["-vV"], root),
        "encoded_rustflags": env::var("CARGO_ENCODED_RUSTFLAGS").ok(), "rustflags": env::var("RUSTFLAGS").ok(),
        "lockfile_keccak256": format!("{:#x}", alloy_primitives::keccak256(include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.lock")))),
        "completed_cases": 0, "checks": CaseStats::default()
    });
    record["build_metadata"] = lean_sphincs_testing::build_metadata();
    write_json(&options.out.join("run.json"), &record)?;
    println!(
        "seed={} start={} cases={} jobs={} backend={} output={}",
        hex::encode(options.seed),
        options.start,
        options.cases,
        options.jobs,
        backend(),
        options.out.display()
    );
    let started = Instant::now();
    let next = Arc::new(AtomicU64::new(0));
    let stop = Arc::new(AtomicBool::new(false));
    let start_index = options.start;
    let case_limit = options.cases;
    let (sender, receiver) = mpsc::sync_channel(options.jobs * 2);
    let mut workers = Vec::new();
    for _ in 0..options.jobs {
        let (next, stop, sender) = (next.clone(), stop.clone(), sender.clone());
        let master = options.seed;
        workers.push(thread::spawn(move || {
            while !stop.load(Ordering::Relaxed) {
                let offset = next.fetch_add(1, Ordering::Relaxed);
                if offset >= case_limit {
                    break;
                }
                let index = start_index + offset;
                let input = generated_case(master, index);
                let outcome = std::panic::catch_unwind(|| check_case(&input, index))
                    .unwrap_or_else(|payload| {
                        let detail = payload
                            .downcast_ref::<String>()
                            .cloned()
                            .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                            .unwrap_or_else(|| "non-string panic payload".to_owned());
                        Err(Failure::new("panic", detail))
                    });
                if outcome.is_err() {
                    stop.store(true, Ordering::Relaxed);
                }
                if sender
                    .send(Event {
                        index,
                        input,
                        outcome,
                    })
                    .is_err()
                {
                    break;
                }
            }
        }));
    }
    drop(sender);
    let mut completed = 0u64;
    let mut totals = CaseStats::default();
    let mut failures = Vec::new();
    for event in receiver {
        match event.outcome {
            Ok(stats) => {
                completed += 1;
                totals.key_comparisons += stats.key_comparisons;
                totals.signature_comparisons += stats.signature_comparisons;
                totals.verification_checks += stats.verification_checks;
                totals.negative_cases += stats.negative_cases;
            }
            Err(failure) => {
                let path = options.out.join(format!("failure-{}.json", event.index));
                write_json(
                    &path,
                    &json!({"master_seed": hex::encode(options.seed), "case_index": event.index, "input": event.input, "failure": failure, "reference_revision": REFERENCE_REVISION, "backend": backend()}),
                )?;
                let mut signing_input = event.input.secret_seed.to_vec();
                signing_input.extend_from_slice(&event.input.message);
                fs::write(path.with_extension("sign"), signing_input)?;
                if let Some(wire) = &failure.wire_hex {
                    fs::write(path.with_extension("wire"), hex::decode(wire)?)?;
                }
                eprintln!(
                    "FAIL case={} {failure}; artifact={}",
                    event.index,
                    path.display()
                );
                failures.push(event.index);
            }
        }
        if completed.is_multiple_of(32) || !failures.is_empty() {
            record["completed_cases"] = json!(completed);
            record["checks"] = json!(totals);
            record["elapsed_seconds"] = json!(started.elapsed().as_secs_f64());
            write_json(&options.out.join("run.json"), &record)?;
            println!(
                "completed {completed}/{}; {:.1}s",
                options.cases,
                started.elapsed().as_secs_f64()
            );
        }
    }
    for worker in workers {
        if worker.join().is_err() {
            failures.push(u64::MAX);
        }
    }
    let success = failures.is_empty() && completed == options.cases;
    record["status"] = json!(if success { "complete" } else { "failed" });
    record["completed_cases"] = json!(completed);
    record["checks"] = json!(totals);
    record["failures"] = json!(failures);
    record["elapsed_seconds"] = json!(started.elapsed().as_secs_f64());
    write_json(&options.out.join("run.json"), &record)?;
    if !success {
        return Err(format!("differential run failed; see {}", options.out.display()).into());
    }
    println!(
        "PASS {completed} randomized cases; {} verification checks; {} negative cases",
        totals.verification_checks, totals.negative_cases
    );
    Ok(())
}

fn main() {
    let result = parse().and_then(|options| options.map_or(Ok(()), run));
    if let Err(error) = result {
        eprintln!("Error: {error}");
        std::process::exit(1);
    }
}
