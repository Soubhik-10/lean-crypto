#!/usr/bin/env python3
"""Extract all production SPHINCS configurations with a compatible Charon.

Extraction produces Rust representations, not correctness proofs. The output
manifest records the exact source snapshot, command and error-free artifact.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
VARIANTS = {
    "sse2": ("-C target-cpu=x86-64", []),
    "avx2": ("-C target-cpu=x86-64-v3", []),
    "sse2-asm": ("-C target-cpu=x86-64", ["--features", "asm-keccak"]),
    "avx2-asm": ("-C target-cpu=x86-64-v3", ["--features", "asm-keccak"]),
    "scalar": (None, ["--target", "aarch64-unknown-linux-gnu"]),
}


def source_snapshot():
    paths = sorted((ROOT / "crates/lean-sphincs/src").rglob("*.rs"))
    paths += [ROOT / "Cargo.toml", ROOT / "Cargo.lock", ROOT / "crates/lean-sphincs/Cargo.toml"]
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
            for p in paths}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charon", type=Path, required=True)
    parser.add_argument("--variant", choices=VARIANTS, action="append")
    parser.add_argument("--target-dir", type=Path)
    args = parser.parse_args()
    charon = args.charon.resolve(strict=True)
    run_root = ROOT / "formal/.cache/extraction-runs" / str(time.time_ns())
    run_root.mkdir(parents=True)
    print(run_root, flush=True)
    tool = {"reported_version": subprocess.check_output([str(charon), "version"], text=True).strip(),
            "binary_sha256": hashlib.sha256(charon.read_bytes()).hexdigest(),
            "driver_sha256": hashlib.sha256(charon.with_name("charon-driver").read_bytes()).hexdigest(),
            "sysroot": "default"}
    before = source_snapshot()
    manifests = []
    pin = json.loads((ROOT / "formal/extractor.json").read_text(encoding="utf-8"))
    for name in args.variant or VARIANTS:
        flags, extra = VARIANTS[name]
        output = run_root / name
        output.mkdir()
        env = os.environ.copy()
        env.pop("CARGO_ENCODED_RUSTFLAGS", None)
        if flags is None:
            env["RUSTFLAGS"] = ""
        else:
            env["RUSTFLAGS"] = flags
        env["CARGO_TARGET_DIR"] = str((args.target_dir or (ROOT / "formal/.cache/extraction-targets")) / name)
        command = [str(charon), "cargo", "--sysroot", "default", "--preset", "aeneas",
                   "--error-on-warnings", "--dest-file", str(output / "lean_sphincs.llbc"),
                   "--", "--lib", "-p", "lean-sphincs", "--no-default-features", "--locked", *extra]
        with (output / "charon.log").open("w", encoding="utf-8") as log:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError("extraction failed: " + name + "\n" + (output / "charon.log").read_text(encoding="utf-8"))
        artifact = output / "lean_sphincs.llbc"
        data = artifact.read_bytes()
        result = json.loads(data)
        if result["charon_version"] != pin["charon"]["version"]:
            raise RuntimeError("Charon version differs from the pinned toolchain: " + name)
        if result["has_errors"]:
            raise RuntimeError("extraction contains errors: " + name)
        if before != source_snapshot():
            raise RuntimeError("source changed during extraction")
        translated = result["translated"]
        if translated["crate_name"] != "lean_sphincs":
            raise RuntimeError("unexpected extracted crate: " + name)
        manifests.append({"variant": name, "command": command, "rustflags": flags,
                          "charon_version": result["charon_version"], "has_errors": False,
                          "sha256": hashlib.sha256(data).hexdigest(),
                          "target": translated["target_information"],
                          "functions": len(translated["fun_decls"]), "types": len(translated["type_decls"])})
        print("Extracted", name, "without errors")
    (run_root / "manifest.json").write_text(json.dumps({"scope": "extraction only; no correctness claim",
        "sources": before, "charon_binary": tool, "variants": manifests}, indent=2) + "\n", encoding="utf-8")
    print(run_root)


if __name__ == "__main__":
    main()
