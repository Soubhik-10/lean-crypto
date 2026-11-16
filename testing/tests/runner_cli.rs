use std::{
    fs,
    path::PathBuf,
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "lean-sphincs-cli-test-{}-{stamp}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn invalid_campaign_options_fail_before_creating_results() {
    for args in [["--cases", "0"], ["--jobs", "0"], ["--seed", "abcd"]] {
        let output = Command::new(env!("CARGO_BIN_EXE_differential"))
            .args(args)
            .output()
            .unwrap();
        assert!(!output.status.success());
    }
}

#[test]
fn parallel_replay_at_end_of_u64_range_runs_exactly_one_case() {
    let directory = Directory::new();
    let output_path = directory.0.join("result");
    let mut child = Command::new(env!("CARGO_BIN_EXE_differential"))
        .args([
            "--seed",
            &"42".repeat(32),
            "--start",
            "18446744073709551614",
            "--cases",
            "1",
            "--jobs",
            "4",
            "--out",
        ])
        .arg(&output_path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let start = Instant::now();
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if start.elapsed() > Duration::from_secs(60) {
            child.kill().unwrap();
            let _ = child.wait();
            panic!("campaign did not stop at the requested range boundary");
        }
        thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let summary: serde_json::Value =
        serde_json::from_slice(&fs::read(output_path.join("run.json")).unwrap()).unwrap();
    assert_eq!(summary["status"], "complete");
    assert_eq!(summary["requested_cases"], 1);
    assert_eq!(summary["completed_cases"], 1);
    assert_eq!(summary["checks"]["key_comparisons"], 1);
    assert_eq!(summary["checks"]["signature_comparisons"], 1);
    assert_eq!(summary["checks"]["verification_checks"], 56);
    assert!(
        summary["build_metadata"]["compiled_source_keccak256"]
            .as_str()
            .unwrap()
            .starts_with("0x")
    );
}
