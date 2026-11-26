"""Check the verifier's exact native reference and Lean toolchain before CI uses it."""
import argparse
import hashlib
import json
import re
import subprocess
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOLCHAIN = "leanprover/lean4:v4.35.0"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reference", type=Path)
    args = parser.parse_args()
    reference = args.reference.resolve()
    pin = json.loads((ROOT / "crates/lean-verifier/reference.json").read_text())
    actual = subprocess.check_output(["git", "-C", str(reference), "rev-parse", "HEAD"], text=True).strip()
    assert actual == pin["revision"], (actual, pin["revision"])
    for name, expected in pin["files"].items():
        assert hashlib.sha256((reference / name).read_bytes()).hexdigest() == expected, name
    workspace = tomllib.loads((ROOT / "Cargo.toml").read_text())
    native = workspace["workspace"]["dependencies"]["lean_vm"]
    assert native["rev"] == actual and native["git"] == pin["repository"]
    crate = tomllib.loads((ROOT / "crates/lean-verifier/Cargo.toml").read_text())
    for name in ("reference-aggregation", "reference-verifier"):
        dependency = crate["dev-dependencies"][name]
        assert dependency["rev"] == actual and dependency["git"] == pin["repository"], name
    profile = (ROOT / "crates/lean-verifier/src/profile.rs").read_text()
    revision = re.search(r'pub const REFERENCE_REVISION: &str\s*=\s*"([0-9a-f]+)";', profile)
    assert revision and revision[1] == actual, "profile reference revision"
    for name in ("Statement", "common", "lean_vm", "lean_xmss", "lean_sphincs", "lean_da"):
        directory = reference / "formal" / name
        assert (directory / "lean-toolchain").read_text().strip() == TOOLCHAIN, name
        config = (directory / "lakefile.toml").read_text()
        assert "skipKernelTC" not in config and "debug." not in config, name
    print(f"Checked {len(pin['files'])} native source digests, profile and Lean pin: {actual}, {TOOLCHAIN}")


if __name__ == "__main__":
    main()
