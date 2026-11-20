#!/usr/bin/env python3
"""Require every production-Rust result to agree with its compiled Lean model."""
import argparse
import json
from pathlib import Path
import re
import subprocess

PUBLIC_KINDS = {"key_gen", "sign", "verify"}
COMPONENT_KINDS = {"indices", "codeword", "digest", "wots", "wots_sign", "fors", "path"}


def expected_lines(manifest, required=PUBLIC_KINDS):
    if manifest.get("schema_version") != 1:
        raise ValueError("unsupported corpus schema")
    cases = manifest.get("cases", [])
    expected = []
    for case in cases:
        kind, name = case["kind"], case["name"]
        if kind not in required or not re.fullmatch(r"[A-Za-z0-9_-]+", name):
            raise ValueError("invalid corpus case")
        expected.append(f"sphincs {kind} {name}: ok")
    if len(expected) != len(set(expected)):
        raise ValueError("duplicate corpus cases")
    for kind in required:
        if not any(case["kind"] == kind for case in cases):
            raise ValueError(f"missing {kind} comparisons")
    return set(expected)


def check_output(manifest, output, required=PUBLIC_KINDS):
    expected = expected_lines(manifest, required)
    lines = output.splitlines()
    if not lines or lines[-1] != "0 mismatches":
        raise ValueError("Lean did not report zero mismatches")
    actual = lines[:-1]
    if len(actual) != len(expected) or set(actual) != expected:
        raise ValueError("Lean did not successfully compare every exported case")
    return len(expected)


def validate_files(corpus, manifest, required):
    expected_lines(manifest, required)
    directory = (corpus / "components" if required == COMPONENT_KINDS else
                 corpus / "lean_sphincs/tests/lean_sphincs/ethlib")
    expected = {directory / case["kind"] / case["name"] / "data.yaml" for case in manifest["cases"]}
    if set(directory.rglob("data.yaml")) != expected:
        raise ValueError("missing or unlisted corpus files")


def run_checked(binary, corpus, manifest, required, log, *flags):
    validate_files(corpus, manifest, required)
    result = subprocess.run([str(binary.resolve()), str(corpus.resolve()), *flags],
                            capture_output=True, text=True, check=False)
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(result.stdout + result.stderr, encoding="utf-8")
    if result.returncode:
        raise ValueError(f"Lean exited with status {result.returncode}; see {log}")
    if result.stderr:
        raise ValueError(f"unexpected Lean diagnostics; see {log}")
    return check_output(manifest, result.stdout, required)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--component-binary", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    args = parser.parse_args()
    public = json.loads((args.corpus / "manifest.json").read_text(encoding="utf-8"))
    components = json.loads((args.corpus / "components.json").read_text(encoding="utf-8"))
    count = run_checked(args.binary, args.corpus, public, PUBLIC_KINDS, args.log, "--sphincs")
    count += run_checked(args.component_binary, args.corpus, components, COMPONENT_KINDS,
                         args.log.with_suffix(".components.log"))
    print(f"Compared all {count} production-Rust results with Lean")


if __name__ == "__main__":
    main()
