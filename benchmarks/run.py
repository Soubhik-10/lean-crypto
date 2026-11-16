#!/usr/bin/env python3
"""Plan, build, explicitly run, and summarize the local Rust benchmark matrix."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
import time

from suite import host, publication, stats

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "benchmarks/evm2/Cargo.toml"
CONFIG = ROOT / "benchmarks/suite/config.json"
BUILD = ROOT / "benchmarks/build"
RESULTS = ROOT / "benchmarks/results"


def source():
    revision = host.command(["git", "rev-parse", "HEAD"])
    dirty = bool(host.command(["git", "status", "--porcelain", "--untracked-files=no"]))
    names = host.command(["git", "ls-files", "--cached", "--others", "--exclude-standard"]).splitlines()
    hashes = {}
    for name in names:
        if name.startswith(("src/", "tests/vectors/", "benchmarks/evm2/", "benchmarks/suite/")) or name in (
            "Cargo.toml", "Cargo.lock", "benchmarks/run.py",
        ):
            path = ROOT / name
            if path.is_file():
                hashes[name] = host.digest(path)
    fingerprint = hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()
    return {"revision": revision, "tracked_changes": dirty, "source_sha256": fingerprint, "files": hashes}


def selected_plan(args, config, capabilities):
    profile = dict(config["profiles"][args.profile])
    for name in ("samples", "sample_ms", "passes"):
        if getattr(args, name, None) is not None:
            profile[name] = getattr(args, name)
    if args.groups:
        profile["groups"] = args.groups.split(",")
    if args.per_fixture:
        profile["per_fixture"] = True
    if not (5 <= profile["samples"] <= 100000 and 10 <= profile["sample_ms"] <= 60000 and 1 <= profile["passes"] <= 100):
        raise ValueError("Need at least 5 samples, 10 ms/sample and one pass")
    if any(group not in ("direct", "macro", "batched", "reject", "hash", "ecrecover") for group in profile["groups"]):
        raise ValueError("Unknown benchmark group")
    if any(group in profile["groups"] for group in ("direct", "batched")) and profile["samples"] % (3 + profile["extra_cases"]):
        raise ValueError("SIMD comparison samples must be a multiple of the corpus size for equal input weighting")
    wanted = set(args.targets.split(",")) if args.targets else {t["id"] for t in config["targets"]}
    unknown = wanted - {t["id"] for t in config["targets"]}
    if unknown:
        raise ValueError(f"Unknown targets: {sorted(unknown)}")
    hashing = set(args.hashing.split(",")) if getattr(args, "hashing", None) else set(config["keccak"])
    recovery = set(args.recovery.split(",")) if getattr(args, "recovery", None) else set(config["ecrecover"])
    if hashing - set(config["keccak"]) or recovery - set(config["ecrecover"]):
        raise ValueError("Unknown hashing backend or recovery provider")
    jobs, skipped = [], []
    if capabilities["architecture"] != "x86_64":
        raise ValueError("This ISA matrix currently requires x86-64")
    for target in config["targets"]:
        if target["id"] not in wanted:
            continue
        missing = [f for f in target["requires"] if not capabilities["features"].get(f, False)]
        if missing:
            skipped.append({"target": target["id"], "reason": "unsupported CPU/OS features", "missing": missing})
            continue
        for keccak in config["keccak"]:
            if keccak not in hashing:
                continue
            for ec in config["ecrecover"]:
                if ec not in recovery:
                    continue
                # PQ and hash work do not depend on the ecrecover provider.
                # The alternate provider therefore gets a recovery-only job.
                groups = profile["groups"] if ec == "libsecp256k1" else ["ecrecover"]
                if ec == "k256" and not any(g in ("macro", "ecrecover") for g in profile["groups"]):
                    continue
                features = []
                if ec == "libsecp256k1":
                    features.append("secp256k1")
                if keccak == "assembly":
                    features.append("asm-keccak")
                if keccak == "tiny":
                    features.append("tiny-keccak")
                if "batched" in groups:
                    features.append("experimental-simd")
                count = ((29 if profile["per_fixture"] else 8) if "macro" in groups else 0)
                count += 6 if "direct" in groups else 0
                count += 3 if "batched" in groups else 0
                count += 16 if "reject" in groups else 0
                count += 42 if "hash" in groups else 0
                count += 1 if "ecrecover" in groups and "macro" not in groups else 0
                jobs.append({
                    "id": f"{target['id']}-{keccak}-{ec}", "target": target,
                    "keccak": keccak, "ecrecover": ec, "features": features,
                    "groups": groups, "case_count": count,
                })
    for job in jobs:
        # LLVM 22 SLP regresses tiny-keccak with AVX2 and AVX-512.
        affected_tiny = (
            job["keccak"] == "tiny"
            and job["target"]["id"] in ("v3", "v4", "native")
            and capabilities["features"].get("avx2", False)
            and not getattr(args, "unmodified_tiny", False)
        )
        if affected_tiny or getattr(args, "disable_slp", False):
            job["id"] += "-no-slp"
            job["extra_rustflags"] = ["-C", "no-vectorize-slp"]
    if not jobs:
        raise ValueError("No supported configurations")
    minimum = sum(j["case_count"] for j in jobs) * profile["samples"] * profile["sample_ms"] * profile["passes"] / 1000
    return {
        "schema_version": 1, "profile_name": args.profile, "profile": profile,
        "toolchain": config["toolchain"], "cpu": args.cpu, "seed": config["seed"],
        "cooldown_seconds": getattr(args, "cooldown_seconds", None) if getattr(args, "cooldown_seconds", None) is not None else profile.get("cooldown_seconds", config["cooldown_seconds"]), "capabilities": capabilities,
        "jobs": jobs, "skipped": skipped, "minimum_sampling_hours": minimum / 3600,
        "duration_note": "Lower bound only; excludes calibration, warmup, fixtures, compilation, long single operations and cooldowns.",
    }


def build_all(plan):
    BUILD.mkdir(parents=True, exist_ok=True)
    original = source()
    index = {
        "schema_version": 1, "created_utc": host.utc(), "source": original,
        "rustc": host.command(["rustc", f"+{plan['toolchain']}", "-vV"]),
        "cargo": host.command(["cargo", f"+{plan['toolchain']}", "-V"]),
        "inherited_rustflags": os.environ.get("RUSTFLAGS"),
        "inherited_encoded_rustflags": os.environ.get("CARGO_ENCODED_RUSTFLAGS"),
        "jobs": {},
    }
    existing_path = BUILD / "builds.json"
    if existing_path.exists():
        existing = json.loads(existing_path.read_text())
        if existing["source"]["source_sha256"] == original["source_sha256"] and existing["rustc"] == index["rustc"]:
            index["jobs"].update(existing["jobs"])
    for job in plan["jobs"]:
        environment = os.environ.copy()
        build_tools = {}
        if os.name == "nt":
            git = shutil.which("git")
            candidate = Path(git).parent.parent / "usr/bin" if git else None
            if candidate and (candidate / "patch.exe").exists():
                environment["PATH"] = str(candidate) + os.pathsep + environment.get("PATH", "")
        # Keep backend selection automatic and record the tools actually used.
        environment.pop("SHA3_ASM_SCRIPT", None)
        for tool in ("perl", "patch"):
            executable = shutil.which(tool, path=environment.get("PATH"))
            if executable:
                build_tools[tool] = {
                    "path": executable,
                    "version": host.command([executable, "--version"], env=environment),
                }

        environment.pop("RUSTFLAGS", None)
        rustflags = ["-C", f"target-cpu={job['target']['cpu']}", *job.get("extra_rustflags", [])]
        environment["CARGO_ENCODED_RUSTFLAGS"] = "\x1f".join(rustflags)
        environment["CARGO_TARGET_DIR"] = str(BUILD / "cargo" / job["target"]["id"])
        environment.update({
            "CARGO_PROFILE_BENCH_LTO": "thin", "CARGO_PROFILE_BENCH_CODEGEN_UNITS": "1",
            "CARGO_PROFILE_BENCH_OPT_LEVEL": "3", "CARGO_PROFILE_BENCH_INCREMENTAL": "false",
        })
        args = ["cargo", f"+{plan['toolchain']}", "build", "--profile", "bench", "--bench", "matrix",
                "--manifest-path", str(MANIFEST), "--locked", "--no-default-features",
                "--message-format=json-render-diagnostics"]
        if job["features"]:
            args += ["--features", ",".join(job["features"])]
        metadata_args = [
            "cargo", f"+{plan['toolchain']}", "metadata", "--format-version", "1",
            "--manifest-path", str(MANIFEST), "--locked", "--no-default-features",
        ]
        if job["features"]:
            metadata_args += ["--features", ",".join(job["features"])]
        metadata = json.loads(host.command(metadata_args, env=environment))
        resolved = {node["id"]: node["features"] for node in metadata["resolve"]["nodes"]}
        feature_graph = [
            {"name": package["name"], "version": package["version"],
             "source": package.get("source"), "features": resolved.get(package["id"], [])}
            for package in metadata["packages"]
        ]
        for package in feature_graph:
            if package["name"] == "alloy-primitives" and "keccak-cache-global" in package["features"]:
                raise RuntimeError("Global hash caching is enabled; publication timings require uncached hashing")

        print(f"Building {job['id']}", flush=True)
        result = subprocess.run(args, cwd=ROOT, env=environment, capture_output=True,
                                text=True, encoding="utf-8", errors="replace")
        (BUILD / f"{job['id']}.build.stdout.log").write_text(result.stdout, encoding="utf-8")
        (BUILD / f"{job['id']}.build.stderr.log").write_text(result.stderr, encoding="utf-8")
        if result.returncode:
            raise RuntimeError(f"Build failed: {job['id']}; see {BUILD}")
        artifacts = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
        assembly_build_logs = []
        for artifact in artifacts:
            if artifact.get("reason") == "build-script-executed" and "sha3-asm" in artifact.get("package_id", ""):
                directory = Path(artifact["out_dir"]).parent
                for name in ("output", "stderr"):
                    path = directory / name
                    if path.exists():
                        assembly_build_logs.append({"file": name, "text": path.read_text(errors="replace")})

        binaries = [a["executable"] for a in artifacts if a.get("reason") == "compiler-artifact"
                    and a.get("target", {}).get("name") == "matrix" and a.get("executable")]
        if len(binaries) != 1:
            raise RuntimeError(f"Expected one matrix executable: {job['id']}")
        # Cargo reuses artifact names across target flag changes; preserve each executable.
        extension = ".exe" if os.name == "nt" else ""
        binary = BUILD / f"{job['id']}{extension}"
        shutil.copy2(binaries[0], binary)
        description = json.loads(host.command([binary, "--describe"]))
        if "direct" in job["groups"] and description["build"]["experimental_adapter"]:
            raise RuntimeError("Raw API measurements must not compile the experimental adapter")
        if description["build"]["keccak_backend"] != job["keccak"]:
            raise RuntimeError("Binary feature configuration mismatch")
        if description["build"]["ecrecover"] != job["ecrecover"]:
            raise RuntimeError("Binary provider configuration mismatch")
        index["jobs"][job["id"]] = {
            "configuration": job, "binary": str(binary), "binary_sha256": host.digest(binary),
            "build": description, "command": args, "resolved_cargo_features": feature_graph, "build_tools": build_tools, "assembly_build_logs": assembly_build_logs,
            "rustflags": rustflags,
            "profile": {"optimization": 3, "lto": "thin", "codegen_units": 1, "incremental": False},
            "cflags": {name: environment.get(name) for name in ("CC", "CFLAGS", "CXX", "CXXFLAGS")},
        }
        host.write_json(BUILD / "builds.json", index)
    if source()["source_sha256"] != original["source_sha256"]:
        raise RuntimeError("Sources changed during compilation")
    return index


def load_builds(plan):
    index = json.loads((BUILD / "builds.json").read_text())
    current = source()
    if current["tracked_changes"]:
        print("Measuring uncommitted sources; exact file hashes are recorded.", flush=True)
    if index["source"]["source_sha256"] != current["source_sha256"]:
        raise RuntimeError("Sources changed; rebuild before measuring")
    for job in plan["jobs"]:
        item = index["jobs"].get(job["id"])
        if not item or item["configuration"] != job or host.digest(item["binary"]) != item["binary_sha256"]:
            raise RuntimeError(f"Missing, stale or mismatched binary: {job['id']}")
    return index


def run_all(plan, args):
    builds = load_builds(plan)
    session = Path(args.session).resolve() if args.session else RESULTS / time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    if session.exists() and not args.resume:
        raise ValueError("Session already exists; use --resume explicitly")
    session.mkdir(parents=True, exist_ok=True)
    state_path = session / "session.json"
    if args.resume:
        state = json.loads(state_path.read_text())
        if state["plan"] != plan or state["source"]["source_sha256"] != source()["source_sha256"]:
            raise ValueError("Resume configuration or source differs")
    else:
        state = {
            "schema_version": 1, "started_utc": host.utc(), "plan": plan,
            "source": source(), "builds": builds, "machine": host.snapshot(plan["cpu"]),
            "completed": {}, "segments": [], "notes": args.notes,
        }
    machine = host.snapshot(plan["cpu"])
    if os.name == "nt":
        for key in ("power_scheme", "processor_power_policy"):
            if machine.get(key) != state["machine"].get(key):
                raise ValueError(f"Machine or power policy changed: {key}; create a new session")
    host.require_same_machine(state["machine"], machine)
    for job in plan["jobs"]:
        if state["builds"]["jobs"][job["id"]]["binary_sha256"] != builds["jobs"][job["id"]]["binary_sha256"]:
            raise ValueError("Binary changed since the session started; create a new session")
    state["segments"].append({"started_utc": host.utc(), "machine": machine})
    host.write_json(state_path, state)
    profile = plan["profile"]
    rng = random.Random(plan["seed"])
    for repeat in range(profile["passes"]):
        jobs = list(plan["jobs"])
        rng.shuffle(jobs)
        for job in jobs:
            task = f"pass-{repeat + 1:02}-{job['id']}"
            path = session / f"{task}.json"
            if task in state["completed"]:
                if host.digest(path) != state["completed"][task]["sha256"]:
                    raise ValueError("Completed raw data changed; create a new session")
                stats.validate(json.loads(path.read_text()), profile["samples"])
                continue
            archive = host.archive_attempt(session, task)
            if archive:
                state.setdefault("attempts", []).append(archive)
                host.write_json(state_path, state)
            print(f"Starting {task}", flush=True)
            binary = builds["jobs"][job["id"]]["binary"]
            command = [
                binary, "--run", "--samples", str(profile["samples"]), "--sample-ms", str(profile["sample_ms"]),
                "--warmup-ms", str(profile["warmup_ms"]), "--seed", str(plan["seed"] + repeat),
                "--extra-cases", str(profile["extra_cases"]), "--groups", ",".join(job["groups"]),
                "--json", str(path), "--corpus-json", str(session / "corpus.json"), "--wait-for-start",
            ]
            if profile["per_fixture"]:
                command.append("--per-fixture")
            before = host.snapshot(plan["cpu"])
            host.require_same_machine(state["machine"], before)
            outcome = host.run_gated(command, cwd=ROOT, env=os.environ.copy(),
                                     cpu=plan["cpu"], stem=path.with_suffix(""))
            host.require_same_machine(before, host.snapshot(plan["cpu"]))
            report = json.loads(path.read_text())
            stats.validate(report, profile["samples"])
            if len(report["measurements"]) != job["case_count"]:
                raise ValueError("Unexpected case count")
            corpus_hash = host.digest(session / "corpus.json")
            if state.get("corpus_sha256", corpus_hash) != corpus_hash:
                raise ValueError("Shared corpus changed")
            state["corpus_sha256"] = corpus_hash
            state["completed"][task] = {
                "configuration": job["id"], "pass": repeat + 1, "file": path.name,
                "sha256": host.digest(path), "machine_before": before, "execution": outcome,
                "binary_sha256": builds["jobs"][job["id"]]["binary_sha256"],
            }
            host.write_json(state_path, state)
            time.sleep(plan["cooldown_seconds"])
    state["finished_utc"] = host.utc()
    host.write_json(state_path, state)
    print(f"Completed session: {session}")


def report_session(args):
    import csv

    session = Path(args.session).resolve()
    state = json.loads((session / "session.json").read_text())
    if not state.get("finished_utc"):
        raise ValueError("Session is incomplete; resume it before publishing results")
    if not 100 <= args.bootstrap <= 100000:
        raise ValueError("Bootstrap resamples must be between 100 and 100000")
    if host.digest(session / "corpus.json") != state["corpus_sha256"]:
        raise ValueError("Shared corpus changed after measurement")
    grouped, reports_by_config, telemetry_by_config = {}, {}, {}
    for task in state["completed"].values():
        path = session / task["file"]
        if host.digest(path) != task["sha256"]:
            raise ValueError("Raw samples changed after recording")
        report = json.loads(path.read_text())
        stats.validate(report, state["plan"]["profile"]["samples"])
        configuration = task["configuration"]
        reports_by_config.setdefault(configuration, []).append(report)
        telemetry_by_config.setdefault(configuration, []).append(path.with_suffix(".telemetry.jsonl"))
        for case in report["measurements"]:
            grouped.setdefault((configuration, case["name"]), []).append(
                [sample["ns_per_op"] for sample in case["samples"]])
    summaries, rows = [], []
    for (configuration, name), passes in sorted(grouped.items()):
        summary = stats.summarize(passes, resamples=args.bootstrap)
        summaries.append({"configuration": configuration, "name": name, **summary})
        if "/reference" in name and not args.include_reference:
            continue
        low, high = summary["median_ci95_ns"]
        rows.append(f"| {configuration} | {name} | {stats.display(summary['median_ns'])} | {stats.display(low)} – {stats.display(high)} | {summary['samples']} |")
    host.write_json(session / "summary.json", summaries)
    with (session / "summary.csv").open("w", newline="", encoding="utf-8") as stream:
        columns = ["configuration", "name", "samples", "passes", "median_ns", "p05_ns",
                   "p95_ns", "p99_ns", "mean_ns", "stdev_ns", "pass_median_spread_percent"]
        writer = csv.DictWriter(stream, fieldnames=columns, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(summaries)
    clock = {configuration: host.telemetry_summary(telemetry_by_config[configuration], reports)
             for configuration, reports in reports_by_config.items()}
    host.write_json(session / "clock-summary.json", clock)
    # Calibrations use the actual recovery measurement from the same configuration.
    # They remain separate from publication tables and do not set protocol gas prices.
    medians = {(row["configuration"], row["name"]): row["median_ns"] for row in summaries}
    calibration = []
    for row in summaries:
        baseline = medians.get((row["configuration"], "macro/evm2/ecrecover"))
        if baseline and "/verify_wire/" in row["name"]:
            ratio = row["median_ns"] / baseline
            calibration.append({
                "configuration": row["configuration"], "name": row["name"],
                "time_ratio_to_ecrecover": ratio, "cpu_ratio_at_3000": 3000 * ratio,
                "cpu_ratio_at_2800": 2800 * ratio, "consensus_price": False,
            })
    host.write_json(session / "calibration.json", calibration)
    draft = publication.render(state, summaries, include_reference=args.include_reference)
    (session / "README-benchmarks.md").write_text(draft, encoding="utf-8")
    print(f"Created {session / 'README-benchmarks.md'}; README.md was not modified")


def report_measurements(args):
    if not 100 <= args.bootstrap <= 100000:
        raise ValueError("Bootstrap resamples must be between 100 and 100000")
    state, summaries = publication.load_measurements(Path(args.measurements), resamples=args.bootstrap)
    output = RESULTS / "published"
    output.mkdir(parents=True, exist_ok=True)
    host.write_json(output / "summary.json", summaries)
    draft = publication.render(state, summaries, include_reference=args.include_reference)
    (output / "README-benchmarks.md").write_text(draft, encoding="utf-8")
    print(f"Created {output / 'README-benchmarks.md'} from recorded samples; no benchmarks ran")



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["plan", "build", "run", "report"])
    parser.add_argument("--profile", choices=["raw", "rust", "quick", "comparison", "publication", "comprehensive", "hashes"], default="rust")
    parser.add_argument("--cpu", type=int, default=2)
    parser.add_argument("--targets", help="baseline,v2,v3,v4,native; default all supported")
    parser.add_argument("--hashing", help="portable,tiny,assembly; default all three")
    parser.add_argument("--recovery", help="libsecp256k1,k256; default both")
    parser.add_argument("--unmodified-tiny", action="store_true", help="Diagnostic only: retain the regressing LLVM SLP code generation for tiny-keccak")
    parser.add_argument("--disable-slp", action="store_true", help="Disable LLVM SLP vectorization for all crates, including Thin LTO")
    parser.add_argument("--groups", help="direct,macro,batched,reject,hash,ecrecover; override the preset")
    parser.add_argument("--samples", type=int)
    parser.add_argument("--sample-ms", type=int)
    parser.add_argument("--passes", type=int)
    parser.add_argument("--cooldown-seconds", type=int, choices=range(0, 3601))
    parser.add_argument("--per-fixture", action="store_true")
    parser.add_argument("--session")
    parser.add_argument("--measurements", help="Reproduce a report from published batch times; report only")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--notes", default="", help="Record boost, cooling, power and ambient conditions")
    parser.add_argument("--bootstrap", type=int, default=2000)
    parser.add_argument("--include-reference", action="store_true", default=True)
    parser.add_argument("--no-reference", action="store_false", dest="include_reference")
    args = parser.parse_args()
    if args.action == "report":
        if bool(args.session) == bool(args.measurements):
            parser.error("report requires either --session or --measurements")
        if args.measurements:
            report_measurements(args)
        else:
            report_session(args)
        return
    if args.measurements:
        parser.error("--measurements is only available for report")
    config = json.loads(CONFIG.read_text())
    capabilities = host.probe(config["toolchain"])
    plan = selected_plan(args, config, capabilities)
    if args.action == "plan":
        print(json.dumps(plan, indent=2))
    elif args.action == "build":
        build_all(plan)
    else:
        with host.cpu_lock(plan["cpu"]):
            run_all(plan, args)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, RuntimeError) as error:
        print(f"Error: {error}", file=sys.stderr)
        sys.exit(1)
