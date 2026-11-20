#!/usr/bin/env python3
"""Install only this repository's extra modules/targets into the ignored pinned build."""
import hashlib
import json
from pathlib import Path
import shutil

root = Path(__file__).resolve().parents[1]
reference = root / "formal/.cache/leanVM/formal/lean_sphincs"
config = reference / "lakefile.toml"
marker = "\n# Local implementation proof targets (prepare_formal.py)\n"
original = config.read_text(encoding="utf-8").split(marker)[0]
pin = json.loads((root / "formal/upstream.json").read_text())
assert (reference / "lean-toolchain").read_text().strip() == pin["toolchain"]
assert "skipKernelTC" not in original and "debug." not in original
shutil.copyfile(root / "formal/Implementation.lean", reference / "Implementation.lean")
shutil.copytree(root / "formal/Implementation", reference / "Implementation", dirs_exist_ok=True)
# Reuse the exact pinned CLI definitions and compiler-replacement proofs, excluding
# only its global main, so the component executable can have its own entry point.
cli = (reference / "cli/SignatureKat.lean").read_text(encoding="utf-8")
entry = "open SignatureKat in\ndef main"
assert cli.count(entry) == 1, "pinned CLI entry point changed"
(reference / "Implementation/ReferenceCli.lean").write_text(cli.split(entry)[0], encoding="utf-8")

config.write_text(original + marker + '''
[[lean_lib]]
name = "Implementation"
roots = ["Implementation", "Implementation.Axioms"]

[[lean_exe]]
name = "implementation-kat"
root = "Implementation.Compare"
''', encoding="utf-8")
files = sorted((root / "formal/Implementation").glob("*.lean")) + [root / "formal/Implementation.lean"]
provenance = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(root / "formal/.cache/implementation-sources.json").write_text(json.dumps(provenance, indent=2) + "\n")
