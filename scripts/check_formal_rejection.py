#!/usr/bin/env python3
"""Prove that real compiled Lean executables reject deliberately wrong expectations."""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from run_formal import PUBLIC_KINDS, COMPONENT_KINDS, check_output


def check(binary, corpus, manifest_name, kinds, log, public):
    manifest = json.loads((corpus / manifest_name).read_text())
    selected = [next(c for c in manifest["cases"] if c["kind"] == kind) for kind in sorted(kinds)]
    # Use a parsable Boolean case for the public gate and an accepted codeword for components.
    target_kind = "verify" if public else "codeword"
    source_root = Path("lean_sphincs/tests/lean_sphincs/ethlib") if public else Path("components")
    target = next(c for c in manifest["cases"] if c["kind"] == target_kind and
                  "output: null" not in (corpus / source_root / c["kind"] / c["name"] / "data.yaml").read_text())
    selected = [target if c["kind"] == target_kind else c for c in selected]
    mini = {"schema_version": 1, "cases": selected}
    with tempfile.TemporaryDirectory(prefix="lean-rejection-") as directory:
        root = Path(directory)
        for case in selected:
            relative = source_root / case["kind"] / case["name"] / "data.yaml"
            destination = root / relative
            destination.parent.mkdir(parents=True)
            shutil.copyfile(corpus / relative, destination)
        path = root / source_root / target["kind"] / target["name"] / "data.yaml"
        original = path.read_text()
        replacement = "false" if "output: 'true'" in original else "true" if public else "0x00"
        changed, count = re.subn(r"^output:.*$", "output: '" + replacement + "'", original, flags=re.M)
        assert count == 1 and changed != original
        path.write_text(changed)
        result = subprocess.run([str(binary.resolve()), str(root)] + (["--sphincs"] if public else []),
                                capture_output=True, text=True, check=False)
        log.write_text(result.stdout + result.stderr)
        if result.returncode == 0 or ": MISMATCH" not in result.stdout:
            raise RuntimeError("the real Lean executable did not reject the wrong expectation")
        try:
            check_output(mini, result.stdout, kinds)
        except ValueError:
            pass
        else:
            raise RuntimeError("the comparison gate accepted the wrong expectation")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--component-binary", type=Path, required=True)
    parser.add_argument("--log-directory", type=Path, required=True)
    args = parser.parse_args()
    args.log_directory.mkdir(parents=True, exist_ok=True)
    check(args.binary, args.corpus, "manifest.json", PUBLIC_KINDS,
          args.log_directory / "rejected-public.log", True)
    check(args.component_binary, args.corpus, "components.json", COMPONENT_KINDS,
          args.log_directory / "rejected-components.log", False)
    print("Both real Lean executables rejected deliberately incorrect expected results")


if __name__ == "__main__":
    main()
