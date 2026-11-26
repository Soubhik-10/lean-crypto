#!/usr/bin/env python3
"""Attempt strict Aeneas translation of a complete, fresh SPHINCS extraction run.

Success is a translation result, not an implementation-correctness proof. Every
variant is attempted, all failures are retained, and any failure exits nonzero.
"""
import argparse
import hashlib
import importlib.util
import json
import re
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("extract_sphincs", ROOT / "scripts/extract_sphincs.py")
extraction = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extraction)


def load_extraction(source_run):
    manifest = json.loads((source_run / "manifest.json").read_text(encoding="utf-8"))
    if manifest["sources"] != extraction.source_snapshot():
        raise RuntimeError("production source differs from the extraction snapshot")
    if manifest.get("charon_binary", {}).get("sysroot") != "default":
        raise RuntimeError("extraction must use the pinned default Rust sysroot")
    variants = manifest["variants"]
    names = [v["variant"] for v in variants]
    if len(names) != len(extraction.VARIANTS) or set(names) != set(extraction.VARIANTS):
        raise RuntimeError("translation gate requires all production configurations exactly once")
    pin = json.loads((ROOT / "formal/extractor.json").read_text(encoding="utf-8"))
    for variant in variants:
        name = variant["variant"]
        data = (source_run / name / "lean_sphincs.llbc").read_bytes()
        if hashlib.sha256(data).hexdigest() != variant["sha256"]:
            raise RuntimeError("extraction artifact hash differs: " + name)
        llbc = json.loads(data)
        if llbc["has_errors"] is not False or variant["has_errors"] is not False:
            raise RuntimeError("extraction artifact contains errors: " + name)
        if llbc["translated"]["crate_name"] != "lean_sphincs":
            raise RuntimeError("unexpected extracted crate: " + name)
        if llbc["charon_version"] != pin["charon"]["version"]:
            raise RuntimeError("Charon version differs from the pinned toolchain: " + name)
    return manifest


def inspect_bindings(destination):
    """Distinguish generated files from complete, assumption-free proof inputs."""
    metadata = destination / "translation.json"
    problems = []
    external_models = []
    if not metadata.exists():
        problems.append("missing translation.json declaration inventory")
    else:
        inventory = json.loads(metadata.read_text(encoding="utf-8"))
        if inventory.get("crate") != "lean_sphincs":
            problems.append("unexpected translated crate")
        functions = inventory.get("functions", [])
        local = {f["rust_name"]: f for f in functions if f.get("is_local")}
        for name in ("lean_sphincs::verify", "lean_sphincs::signing::key_gen", "lean_sphincs::signing::sign"):
            if name not in local:
                problems.append("missing public entry point: " + name)
        for name, function in local.items():
            if function.get("is_opaque"):
                problems.append("opaque local function: " + name)
    for path in sorted(destination.rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        if path.stem.endswith("_Template"):
            external_models.extend(re.findall(r"^axiom\s+([^\s:(]+)", source, re.MULTILINE))
        elif re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|opaque)\s", source, re.MULTILINE):
            problems.append("unproved declaration or proof hole: " + str(path.relative_to(destination)))
    return problems, external_models



def binding_hashes(destination):
    paths = [*destination.rglob("*.lean"), destination / "translation.json"]
    return {p.relative_to(destination).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths) if p.is_file()}


def load_translation(destination):
    """Bind checked Lean bodies to the current extraction, pins and source bytes."""
    report = json.loads((destination / "report.json").read_text(encoding="utf-8"))
    pin = json.loads((ROOT / "formal/extractor.json").read_text(encoding="utf-8"))
    if report["requested_toolchain"] != pin:
        raise RuntimeError("translation toolchain pin changed")
    source_run = (ROOT / report["extraction_run"]).resolve(strict=True)
    if not source_run.is_relative_to((ROOT / "formal/.cache/extraction-runs").resolve()):
        raise RuntimeError("unexpected extraction path")
    manifest_path = source_run / "manifest.json"
    if hashlib.sha256(manifest_path.read_bytes()).hexdigest() != report["extraction_manifest_sha256"]:
        raise RuntimeError("extraction manifest hash differs")
    manifest = load_extraction(source_run)
    if report["sources"] != manifest["sources"]:
        raise RuntimeError("translation source snapshot is stale")
    results = report["results"]
    if (len(results) != len(extraction.VARIANTS) or
            {r["variant"] for r in results} != set(extraction.VARIANTS)):
        raise RuntimeError("all production configurations are required exactly once")
    if not report["translation_passed"] or any(not r["translated"] for r in results):
        raise RuntimeError("strict translation did not pass")
    for result in results:
        generated = destination / result["variant"]
        if binding_hashes(generated) != result["generated_sha256"]:
            raise RuntimeError("translated body or declaration inventory hash differs: " + result["variant"])
        problems, _ = inspect_bindings(generated)
        if problems:
            raise RuntimeError("incomplete translated bindings: " + "; ".join(problems))
    return report


def summarize(result, destination):
    # Aeneas can emit ANSI color codes even when its output is redirected.
    plain = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout)
    diagnostics = [line for line in plain.splitlines()
                   if line.startswith(("[Error]", "[Warn", "Source:", "Definition span:"))]
    generated = sorted(str(p.relative_to(destination)) for p in destination.rglob("*.lean"))
    problems, _ = inspect_bindings(destination)
    diagnostics.extend(problems)
    success = result.returncode == 0 and not diagnostics and bool(generated)
    return success, diagnostics, generated


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aeneas", type=Path, required=True)
    parser.add_argument("--extraction-run", type=Path, required=True)
    args = parser.parse_args()
    aeneas = args.aeneas.resolve(strict=True)
    source_run = args.extraction_run.resolve(strict=True)
    manifest = load_extraction(source_run)
    variants = manifest["variants"]
    tool_hash = hashlib.sha256(aeneas.read_bytes()).hexdigest()
    tool_version = subprocess.run([str(aeneas), "-version"], text=True, check=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout.strip()
    output = ROOT / "formal/.cache/translation-runs" / str(time.time_ns())
    output.mkdir(parents=True)
    print(output, flush=True)
    results = []
    for variant in variants:
        name = variant["variant"]
        llbc = source_run / name / "lean_sphincs.llbc"
        destination = output / name
        destination.mkdir()
        command = [str(aeneas), "-backend", "lean", "-split-files", "-gen-lib-entry", "-emit-json",
                   "-warnings-as-errors", "-no-progress-bar", "-sequential", "-max-error-spans", "2",
                   "-dest", str(destination), str(llbc)]
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
        (destination / "aeneas.log").write_text(result.stdout, encoding="utf-8")
        success, diagnostics, generated = summarize(result, destination)
        results.append({"variant": name, "exit_code": result.returncode,
                        "translated": success, "diagnostics": diagnostics,
                        "generated_lean_files": generated,
                        "generated_sha256": binding_hashes(destination),
                        "external_models_required": inspect_bindings(destination)[1],
                        "proof_ready": success and not inspect_bindings(destination)[1],
                        "command": command})
        print(name + (": translated" if success else ": FAILED"), flush=True)
    if manifest["sources"] != extraction.source_snapshot():
        raise RuntimeError("production source changed during translation")
    passed = all(r["translated"] for r in results)
    report = {"scope": "strict Rust-to-Lean translation gate; no correctness proof",
              "translation_passed": passed, "full_crate_formally_verified": False,
              "requested_toolchain": json.loads((ROOT / "formal/extractor.json").read_text(encoding="utf-8")),
              "aeneas_binary": {"sha256": tool_hash, "reported_version": tool_version},
              "extraction_run": source_run.relative_to(ROOT).as_posix(),
              "extraction_manifest_sha256": hashlib.sha256((source_run / "manifest.json").read_bytes()).hexdigest(),
              "sources": manifest["sources"], "results": results}
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(output / "report.json", flush=True)
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
