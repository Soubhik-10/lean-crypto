"""Run the pinned Lean drivers against this port; crashes never count as rejections."""
import argparse
import importlib.util
import subprocess
import sys
from pathlib import Path


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def invoke(module, args):
    sys.argv = [str(module.__file__), *map(str, args)]
    try:
        module.main()
    except SystemExit as error:
        if error.code not in (None, 0):
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reference", type=Path)
    parser.add_argument("fixtures", type=Path)
    parser.add_argument("rust", type=Path)
    parser.add_argument("--models", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--mutations", type=int, default=256)
    args = parser.parse_args()
    reference, fixtures, rust, models, output = (p.resolve() for p in
        (args.reference, args.fixtures, args.rust, args.models, args.output))
    output.mkdir(parents=True, exist_ok=True)
    directories = sorted(p for p in fixtures.iterdir() if p.is_dir())
    assert directories, "empty fixture corpus"
    # Exercise both transports of every honest proof before mutation testing.
    commands = []
    for directory in directories:
        base = [directory / "bytecode.bin", directory / "public_input.bin"]
        commands += [base + [directory / "proof.wire"],
                     base + [directory / "stream.bin", directory / "merkle_phases.bin"]]
    sys.path.insert(0, str(reference / "formal/lean_vm/scripts"))
    import proofio
    verdicts = proofio.batch(rust, commands, 10, strict=True)
    assert all(v == "accept" for v in verdicts), verdicts
    for command in commands:
        # These small native fixtures must finish; a resource failure fails CI.
        result = subprocess.run([str(models / "leanvm-verify"), *map(str, command)],
                                capture_output=True, text=True, timeout=300, check=True,
                                preexec_fn=proofio.limit(10))
        assert "verification succeeded" in result.stdout, result.stdout
    print(f"Accepted {len(commands)} honest wire/structured cases in Rust and Lean", flush=True)
    fuzz = load(reference / "formal/lean_vm/scripts/fuzz-verifier.py", "verifier_fuzz")
    log = output / "verifier.tsv"
    invoke(fuzz, [fixtures, "--lean-exe", models / "leanvm-verify", "--rust-exe", rust,
                  "--jobs", args.jobs, "--mutations", args.mutations, "--seed", 1,
                  "--memory-gb", 10, "--timeout", 300,
                  "--keep", output / "verifier-failures", "--log", log])
    rows = [line.split("\t") for line in log.read_text().splitlines()]
    assert len(rows) == len(directories) * args.mutations, "missing verdicts"
    for row in rows:
        assert row[4] in ("accept", "reject") and row[6] in ("accept", "reject"), row
        assert row[4] == row[6], row
        if row[2] == "honest":
            assert row[4] == "accept", row
    wire = load(reference / "formal/lean_vm/scripts/wire-diff.py", "verifier_wire")
    wire.LEAN_EXE, wire.RUST_EXE = models / "wire-diff", rust
    invoke(wire, [fixtures, "--jobs", args.jobs, "--all-phases", "--random", 16,
                  "--seed", 1, "--memory-gb", 10,
                  "--keep", output / "wire-failures", "--log", output / "wire.tsv"])
    print("Verifier and wire conformance passed without crashes", flush=True)


if __name__ == "__main__":
    main()
