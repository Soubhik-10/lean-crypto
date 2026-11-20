#!/usr/bin/env python3
"""Run the pinned Lean model and reject skipped, incomplete or mismatched comparisons."""

import argparse
import json
from pathlib import Path
import re
import subprocess


def expected_lines(manifest):
    if manifest.get("schema_version") != 1:
        raise ValueError("unsupported corpus schema")
    cases = manifest.get("cases", [])
    expected = []
    for case in cases:
        kind, name = case["kind"], case["name"]
        if kind not in {"key_gen", "sign", "verify"} or not re.fullmatch(r"[A-Za-z0-9_-]+", name):
            raise ValueError("invalid corpus case")
        expected.append(f"sphincs {kind} {name}: ok")
    if len(expected) != len(set(expected)):
        raise ValueError("duplicate corpus cases")
    for kind in ("key_gen", "sign", "verify"):
        if not any(case["kind"] == kind for case in cases):
            raise ValueError(f"missing {kind} comparisons")
    return set(expected)


def check_output(manifest, output):
    expected = expected_lines(manifest)
    lines = output.splitlines()
    actual = [line for line in lines if line.startswith("sphincs ")]
    if len(actual) != len(expected) or set(actual) != expected:
        raise ValueError("Lean did not successfully compare every exported case")
    if not lines or lines[-1] != "0 mismatches":
        raise ValueError("Lean did not report zero mismatches")
    return len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--log", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads((args.corpus / "manifest.json").read_text(encoding="utf-8"))
    expected_lines(manifest)
    for case in manifest["cases"]:
        path = args.corpus / "lean_sphincs/tests/lean_sphincs/ethlib" / case["kind"] / case["name"] / "data.yaml"
        if not path.is_file():
            raise ValueError(f"missing corpus input: {path}")
    result = subprocess.run(
        [str(args.binary.resolve()), str(args.corpus.resolve()), "--sphincs"],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    args.log.parent.mkdir(parents=True, exist_ok=True)
    args.log.write_text(result.stdout, encoding="utf-8")
    print(result.stdout, end="")
    result.check_returncode()
    count = check_output(manifest, result.stdout)
    print(f"Compared all {count} Rust results with the Lean model; seed {manifest['seed']}")


if __name__ == "__main__":
    main()
