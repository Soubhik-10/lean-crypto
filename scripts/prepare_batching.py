#!/usr/bin/env python3
"""Fetch hash-pinned EthLib source files for the standalone batching proof package."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import urllib.request

ROOT = Path(__file__).resolve().parents[1]


def prepare(offline=False):
    pin = json.loads((ROOT / "formal/ethlib.json").read_text(encoding="utf-8"))
    if pin["repository"] != "ethereum/EthLib" or not re.fullmatch(r"[0-9a-f]{40}", pin["revision"]):
        raise ValueError("unexpected specification identity")
    if (ROOT / "formal/lean-toolchain").read_text(encoding="utf-8-sig").strip() != pin["toolchain"]:
        raise ValueError("batching proof toolchain differs from its specification pin")
    cache = ROOT / "formal/.cache/ethlib"
    for name, expected in pin["files"].items():
        path = Path(name)
        if path.is_absolute() or ".." in path.parts or not name.startswith("EthLib/") or path.suffix != ".lean":
            raise ValueError("unexpected specification path: " + name)
        if not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError("invalid specification digest: " + name)
        target = cache / path
        if target.exists():
            data = target.read_bytes()
        elif offline:
            raise ValueError("missing cached specification: " + name)
        else:
            url = "https://raw.githubusercontent.com/" + pin["repository"] + "/" + pin["revision"] + "/" + name
            with urllib.request.urlopen(url, timeout=60) as response:
                data = response.read()
        if hashlib.sha256(data).hexdigest() != expected:
            raise ValueError("specification source hash mismatch: " + name)
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists():
            target.write_bytes(data)
    print("Verified", len(pin["files"]), "unchanged EthLib modules at", pin["revision"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true")
    args = parser.parse_args()
    prepare(args.offline)
