#!/usr/bin/env python3
"""Check complete SPHINCS source functional refinement against the pinned interface models."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("extract_sphincs", ROOT / "scripts/extract_sphincs.py")
extraction = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extraction)


translation_spec = importlib.util.spec_from_file_location("translate_sphincs", ROOT / "scripts/translate_sphincs.py")
translation = importlib.util.module_from_spec(translation_spec)
translation_spec.loader.exec_module(translation)


runtime_spec = importlib.util.spec_from_file_location("prepare_rust_runtime", ROOT / "scripts/prepare_rust_runtime.py")
runtime_models = importlib.util.module_from_spec(runtime_spec)
runtime_spec.loader.exec_module(runtime_models)


reference_spec = importlib.util.spec_from_file_location("prepare_batching", ROOT / "scripts/prepare_batching.py")
reference = importlib.util.module_from_spec(reference_spec)
reference_spec.loader.exec_module(reference)


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def checked(command, cwd, log, env):
    with log.open("w", encoding="utf-8") as output:
        result = subprocess.run([str(x) for x in command], cwd=cwd, env=env,
                                stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(str(log) + "\n" + log.read_text(encoding="utf-8"))
    return log.read_text(encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--translation-run", required=True, type=Path)
    parser.add_argument("--proof-workspace", required=True, type=Path)
    parser.add_argument("--jobs", type=int, default=2, help="Independent configuration checks in parallel (1 to 5)")
    args = parser.parse_args()
    if not 1 <= args.jobs <= len(extraction.VARIANTS):
        parser.error("--jobs must be between 1 and 5")
    runtime = args.runtime.resolve(strict=True)
    translated = args.translation_run.resolve(strict=True)
    workspace = args.proof_workspace.resolve()
    if not any(workspace.is_relative_to(base) for base in
               [(ROOT / "formal/.cache").resolve(), runtime]):
        raise RuntimeError("proof workspace must stay inside the runtime or formal cache")
    reference.prepare(offline=True)
    report = translation.load_translation(translated)
    report_sha256 = hashlib.sha256((translated / "report.json").read_bytes()).hexdigest()
    snapshot = extraction.source_snapshot()
    variants = report["results"]
    pin = report["requested_toolchain"]
    backend = ROOT / "formal/.cache" / ("aeneas-" + pin["aeneas"]["revision"]) / "backends/lean"
    def tree_hashes(root):
        return {p.relative_to(root).as_posix(): digest(p) for p in root.rglob("*.lean")
                if ".lake" not in p.relative_to(root).parts}
    if tree_hashes(backend) != tree_hashes(runtime / "packages/aeneas"):
        raise RuntimeError("Aeneas runtime differs from the pinned backend")
    stdlib_model = runtime_models.validate_stdlib_model(runtime, backend)
    proof_files = [ROOT / "formal/Batching/Keccak.lean", ROOT / "formal/Batching/Constants.lean",
                   *sorted((ROOT / "formal/Runtime").rglob("*.lean")),
                   *sorted((ROOT / "formal/RustCrypto").rglob("*.lean"))]
    proof_contents = {p: p.read_bytes() for p in proof_files}
    before = {p.relative_to(ROOT).as_posix(): hashlib.sha256(data.replace(b"\r\n", b"\n")).hexdigest()
              for p, data in proof_contents.items()}
    pipeline_files = [ROOT / "scripts" / name for name in
                      ["extract_sphincs.py", "translate_sphincs.py", "check_sphincs_source.py",
                       "prepare_rust_runtime.py", "prepare_batching.py"]]
    pipeline_files += [ROOT / "formal" / name for name in ["ethlib.json", "extractor.json", "lean-toolchain", "lakefile.toml"]]
    pipeline_before = {p.relative_to(ROOT).as_posix(): digest(p) for p in pipeline_files}
    for path in proof_files:
        if re.search(r"\b(?:sorry|admit|axiom|native_decide)\b|skipKernelTC|ofReduceBool|implemented_by",
                     proof_contents[path].decode("utf-8")):
            raise RuntimeError("unproved model or proof escape: " + str(path))
    output = ROOT / "formal/.cache/source-runs" / str(time.time_ns())
    output.mkdir(parents=True)
    workspace = workspace / output.name
    print(output, flush=True)
    base_env = os.environ.copy()
    lake_paths = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=runtime,
                                        text=True).strip().split(os.pathsep)
    lake_paths = [str((runtime / p).resolve()) if not Path(p).is_absolute() else p for p in lake_paths]
    stock_lib = str(runtime / "packages/aeneas/.lake/build/lib/lean")
    if stock_lib not in lake_paths:
        raise RuntimeError("stock runtime library is missing from Lean search path")
    lake_paths = [str(runtime / "stdlib-model/.lake/build/lib/lean") if path == stock_lib else path
                  for path in lake_paths]
    def check_variant(variant):
        env = base_env.copy()
        controls = {}
        label = variant["variant"]
        folder = workspace / label
        logs = output / label
        for sub in [folder / "LeanSphincs", folder / "RustCrypto", logs]:
            sub.mkdir(parents=True, exist_ok=True)
        generated = translated / label
        inputs = {name: (generated / name).read_bytes() for name in ["Types.lean", "Funs.lean", "translation.json"]}
        if any(hashlib.sha256(data).hexdigest() != variant["generated_sha256"][name] for name, data in inputs.items()):
            raise RuntimeError("translated body or inventory changed before checking: " + label)
        metadata = json.loads(inputs["translation.json"])
        local = [f for f in metadata["functions"] if f["is_local"]]
        if not local or any(f["is_opaque"] for f in local):
            raise RuntimeError("missing or opaque local body: " + label)
        body_hashes = {name: hashlib.sha256(inputs[name]).hexdigest() for name in ["Types.lean", "Funs.lean"]}
        for name in body_hashes:
            (folder / "LeanSphincs" / name).write_bytes(inputs[name])
        for file in proof_files:
            target = folder / file.relative_to(ROOT / "formal")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(proof_contents[file])
        for name in ["TypesExternal", "FunsExternal"]:
            (folder / "LeanSphincs" / (name + ".lean")).write_bytes(
                proof_contents[ROOT / "formal/RustCrypto/Models" / (name + ".lean")])
        variant_proofs = ['RustCrypto/Fors/Scalar/Body', 'RustCrypto/Fors/Scalar/Loop', 'RustCrypto/Fors/Scalar/Full', 'RustCrypto/Fors/Scalar/ShortBody', 'RustCrypto/Fors/Scalar/ShortLoop', 'RustCrypto/Fors/Scalar/Total'] if label == "scalar" else []
        if label != "scalar":
            variant_proofs = ["RustCrypto/Hash/Batch/AppendNodes", "RustCrypto/Hash/Keccak/Rotate", "RustCrypto/Hash/Keccak/Rotations", "RustCrypto/Hash/Keccak/RoundConstants",
                              "RustCrypto/Hash/Keccak/Permutation", "RustCrypto/Hash/Keccak/WordBridge",
                              "RustCrypto/Hash/Keccak/Bridge", "RustCrypto/Hash/Keccak/Loop",
                              "RustCrypto/Hash/Keccak/Short/Load", "RustCrypto/Hash/Keccak/Short/Store",
                              "RustCrypto/Hash/Keccak/Short/Padding", "RustCrypto/Hash/Keccak/Short/Hash",
                              "RustCrypto/Hash/Batch/Nodes", "RustCrypto/Hash/Batch/Parents", "RustCrypto/Hash/Batch/Positions",
                              "RustCrypto/Fors/Batch/Read", "RustCrypto/Fors/Batch/FromFn", "RustCrypto/Fors/Batch/Step", "RustCrypto/Fors/Batch/Walk", "RustCrypto/Fors/Batch/Source", "RustCrypto/Fors/Batch/Bridge", "RustCrypto/Fors/OpeningBytes", "RustCrypto/Fors/Batch/Leaf", "RustCrypto/Fors/Batch/Full",
                              "RustCrypto/Fors/Forest/Closures", "RustCrypto/Fors/Forest/Read", "RustCrypto/Fors/Forest/Model", "RustCrypto/Fors/Forest/Body", "RustCrypto/Fors/Forest/Prefix", "RustCrypto/Fors/Forest/Loop", "RustCrypto/Fors/Forest/Full", "RustCrypto/Fors/Forest/Short", "RustCrypto/Fors/Forest/Total", "RustCrypto/Serialization/Layout/ForsSimd"]
            if label.startswith("avx2"):
                for module in [
                    'Hash/Keccak/Permutation',
                    'Hash/Keccak/WordBridge',
                    'Hash/Keccak/Bridge',
                    'Hash/Keccak/Loop',
                    'Hash/Keccak/Short/Load',
                    'Hash/Keccak/Short/Store',
                    'Hash/Keccak/Short/Padding',
                    'Hash/Keccak/Short/Hash',
                    'Hash/Batch/Nodes',
                    'Hash/Batch/Parents',
                    'Hash/Batch/Positions',
                    'Fors/Batch/Read',
                    'Fors/Batch/FromFn',
                    'Fors/Batch/Step',
                    'Fors/Batch/Walk',
                    'Fors/Batch/Source',
                    'Fors/Batch/Bridge',
                    'Fors/OpeningBytes',
                    'Fors/Batch/Leaf',
                    'Fors/Batch/Full',
                    'Fors/Forest/Closures',
                    'Fors/Forest/Read',
                    'Fors/Forest/Model',
                    'Fors/Forest/Body',
                    'Fors/Forest/Prefix',
                    'Fors/Forest/Loop',
                    'Fors/Forest/Full',
                    'Fors/Forest/Short',
                    'Fors/Forest/Total',
                ]:
                    proof_path = folder / "RustCrypto" / (module + ".lean")
                    proof_text = proof_path.read_text(encoding="utf-8")
                    proof_text = proof_text.replace("u64x2", "u64x4")
                    if module == "Hash/Keccak/Permutation":
                        if proof_text.count("abbrev width := 2") != 1 or proof_text.count("Array U64 2#usize") != 1:
                            raise RuntimeError("SIMD proof specialization sites changed")
                        proof_text = proof_text.replace("abbrev width := 2", "abbrev width := 4")
                        proof_text = proof_text.replace("Array U64 2#usize", "Array U64 4#usize")
                    if module.startswith("Hash/Keccak/Short/"):
                        proof_text = re.sub(r"(?<![0-9])2#usize", "4#usize", proof_text)
                        proof_text = re.sub(r"Fin 2(?![0-9])", "Fin 4", proof_text)
                        proof_text = re.sub(r"< 2(?![0-9])", "< 4", proof_text)
                    if module.startswith("Hash/Batch/"):
                        proof_text = re.sub(r"(?<![0-9])2#usize", "4#usize", proof_text)
                        for lhs, rhs in [("< 2", "< 4"), ("≤ 2", "≤ 4"),
                                         ("= 2 :=", "= 4 :="), ("2-state", "4-state")]:
                            proof_text = proof_text.replace(lhs, rhs)
                    if module.startswith("Fors/Batch/") or module == "Fors/OpeningBytes":
                        proof_text = re.sub(r"(?<![0-9])2#usize", "4#usize", proof_text)
                        proof_text = re.sub(r"Fin 2(?![0-9])", "Fin 4", proof_text)
                        proof_text = re.sub(r"< 2(?![0-9])", "< 4", proof_text)
                    if module.startswith("Fors/Forest/"):
                        proof_text = proof_text.replace("abbrev width := 2", "abbrev width := 4")
                        proof_text = re.sub(r"(?<![0-9])2#usize", "4#usize", proof_text)
                        proof_text = re.sub(r"(?<![0-9])352(?![0-9])", "704", proof_text)
                    proof_path.write_text(proof_text, encoding="utf-8")
        if label.startswith("avx2"):
            variant_proofs += ['RustCrypto/Wots/Avx2/Step', 'RustCrypto/Wots/Avx2/Read', 'RustCrypto/Wots/Avx2/ReadFull', 'RustCrypto/Wots/Avx2/Scatter', 'RustCrypto/Wots/Avx2/ScatterNative', 'RustCrypto/Wots/Avx2/Positions', 'RustCrypto/Wots/Avx2/Gather', 'RustCrypto/Wots/Avx2/Group', 'RustCrypto/Wots/Avx2/Queue', 'RustCrypto/Wots/Avx2/QueueFacts', 'RustCrypto/Wots/Avx2/ScanValue', 'RustCrypto/Wots/Avx2/ScanBody', 'RustCrypto/Wots/Avx2/ScanInvariant', 'RustCrypto/Wots/Avx2/ScanLoop', 'RustCrypto/Wots/Avx2/TailBody', 'RustCrypto/Wots/Avx2/TailLoop', 'RustCrypto/Wots/Avx2/RoundValue', 'RustCrypto/Wots/Avx2/RoundBody', 'RustCrypto/Wots/Avx2/Window', 'RustCrypto/Wots/Avx2/Prefix', 'RustCrypto/Wots/Avx2/ChainsBody', 'RustCrypto/Wots/Avx2/ChainsLoop', 'RustCrypto/Wots/Avx2/ChainsShort', 'RustCrypto/Wots/Avx2/ChainsTotal', 'RustCrypto/Wots/Avx2/Entry', 'RustCrypto/Verification/Layer/Avx2']
        if not label.startswith("avx2"):
            variant_proofs += ['RustCrypto/Wots/Scalar/Body', 'RustCrypto/Wots/Scalar/Loop', 'RustCrypto/Wots/Scalar/Short', 'RustCrypto/Wots/Scalar/Chains', 'RustCrypto/Wots/Scalar/Entry', 'RustCrypto/Verification/Layer/Scalar']
        if label == "scalar":
            variant_proofs += ["RustCrypto/Verification/Fors/Scalar", "RustCrypto/Verification/Root/Scalar", "RustCrypto/Correctness/Signing/Scalar"]
        elif label.startswith("avx2"):
            variant_proofs += ["RustCrypto/Verification/Fors/Simd", "RustCrypto/Verification/Root/Avx2", "RustCrypto/Correctness/Signing/Avx2"]
        else:
            variant_proofs += ["RustCrypto/Verification/Fors/Simd", "RustCrypto/Verification/Root/Sse2", "RustCrypto/Correctness/Signing/Sse2"]
        audit_file = folder / "RustCrypto/Audit/Source.lean"
        audit = audit_file.read_text(encoding="utf-8")
        audit = audit.replace("import all LeanSphincs.Funs\n", "import all LeanSphincs.Funs\n" +
            "".join("import all " + module.replace("/", ".") + "\n" for module in variant_proofs), 1)
        audit_file.write_text(audit, encoding="utf-8")
        env["LEAN_PATH"] = os.pathsep.join([str(folder), *lake_paths,
            str(ROOT / "formal/.lake/build/lib/lean")])
        modules = ["Batching/Keccak", "Batching/Constants", "RustCrypto/Models/Parser", "RustCrypto/Models/Simd", "RustCrypto/Models/Compat", "RustCrypto/Common/Chunks",
                   "LeanSphincs/TypesExternal", "LeanSphincs/Types", "LeanSphincs/FunsExternal",
                   "LeanSphincs/Funs", "RustCrypto/Serialization/Parser", "RustCrypto/Serialization/Index", "RustCrypto/Hash/Core", "RustCrypto/Hash/Primitives", "RustCrypto/Verification/Core", "RustCrypto/Serialization/Writer", "RustCrypto/Wots/Encoding/Codeword", "RustCrypto/Wots/Encoding/CodewordBridge", "RustCrypto/Wots/Chain", "RustCrypto/Wots/Encoding/CounterSearch", "RustCrypto/Common/ByteBridge", "RustCrypto/Serialization/ReadBytes", "RustCrypto/Serialization/WriteBytes",
                   "RustCrypto/Common/ByteRelations", "RustCrypto/Signing/Bytes", "RustCrypto/Tree/Climb",
                   "RustCrypto/Wots/Source", "RustCrypto/Common/BigEndian", "RustCrypto/Hash/AddressBridge",
                   "RustCrypto/Hash/TweakableBridge", "RustCrypto/Wots/ChainOrder", "RustCrypto/Wots/Ethlib", "RustCrypto/Hash/DomainFrame", "RustCrypto/Wots/Prf", "RustCrypto/Common/OrderedVector", "RustCrypto/Common/VectorFlatten", "RustCrypto/Wots/Public", "RustCrypto/Wots/PublicLeafBridge", "RustCrypto/Wots/Signing/Source", "RustCrypto/Wots/Signing/Bridge", "RustCrypto/Wots/Encoding/EncodingBridge",
                   "RustCrypto/Wots/Encoding/CounterBridge", "RustCrypto/Wots/Encoding/SearchBridge", "RustCrypto/Wots/Signing/Full", "RustCrypto/Tree/ParentBridge",
                   "RustCrypto/Tree/Primitives", "RustCrypto/Fors/Positions", "RustCrypto/Fors/Primitives", "RustCrypto/Tree/ClimbBridge", "RustCrypto/Fors/Climb",
                   "RustCrypto/Fors/Window", "RustCrypto/Fors/Digest", "RustCrypto/Fors/DigestBridge", "RustCrypto/Tree/Build/Finish", "RustCrypto/Tree/Build/Root", "RustCrypto/Tree/Build/RootBridge", "RustCrypto/Tree/Build/Selection", "RustCrypto/Tree/Build/Secret", "RustCrypto/Tree/Build/SecretBridge", "RustCrypto/Tree/Build/FinishPath", "RustCrypto/Tree/Build/Coverage", "RustCrypto/Tree/Build/PathPatch", "RustCrypto/Tree/Build/Path", "RustCrypto/Tree/Build/RootCoverage", "RustCrypto/Tree/MerklePath",
                   "RustCrypto/Tree/MerkleBuilt", "RustCrypto/Tree/Build/Models", "RustCrypto/Tree/Build/ConstructorPath", "RustCrypto/Tree/Construction",
                   "RustCrypto/Common/OrderedPrefix", "RustCrypto/Fors/Signing/Core", "RustCrypto/Fors/Signing/Loop", "RustCrypto/Fors/Signing/Full",
                   "RustCrypto/Fors/Scalar/Bytes", "RustCrypto/Fors/Scalar/Layout", "RustCrypto/Tree/ClimbShort",
                   "RustCrypto/Wots/Recovery/Model", "RustCrypto/Wots/Recovery/Layout", "RustCrypto/Wots/Recovery/Canonical",
                   "RustCrypto/Wots/Encoding/CounterBytes", "RustCrypto/Wots/Encoding/Read", "RustCrypto/Wots/Backend", "RustCrypto/Wots/Entry", "RustCrypto/Keygen/Material", "RustCrypto/Hash/ContextFrame", "RustCrypto/Keygen/KeyGen", "RustCrypto/Tree/Cache/Model", "RustCrypto/Tree/Cache/Leaf", "RustCrypto/Tree/Cache/LeafLoop", "RustCrypto/Tree/Cache/ParentBody", "RustCrypto/Tree/Cache/Update", "RustCrypto/Tree/Cache/ParentLoop", "RustCrypto/Tree/Cache/LevelsBody", "RustCrypto/Tree/Cache/LevelsLoop", "RustCrypto/Tree/Cache/New", "RustCrypto/Tree/Cache/PathIndex", "RustCrypto/Tree/Cache/Path", "RustCrypto/Verification/Message/Bridge", "RustCrypto/Verification/Message/Full", "RustCrypto/Verification/Message/IndexBridge", "RustCrypto/Verification/Message/IndexMachine", "RustCrypto/Verification/Layer/Input", "RustCrypto/Verification/Layer/Index", "RustCrypto/Verification/Layer/Model", "RustCrypto/Verification/Layer/Short", "RustCrypto/Serialization/Layout/Read", "RustCrypto/Serialization/Layout/Node", "RustCrypto/Serialization/Layout/Counter", "RustCrypto/Serialization/Layout/Digests", "RustCrypto/Serialization/Layout/Layer", "RustCrypto/Serialization/Layout/Opening", "RustCrypto/Serialization/Layout/Fors", "RustCrypto/Serialization/Layout/Signature",
                   "RustCrypto/Formatting/Numeric", "RustCrypto/Formatting/Laws", "RustCrypto/Formatting/Template", "RustCrypto/Formatting/Source", "RustCrypto/Formatting/Output", "RustCrypto/Correctness/Merkle", "RustCrypto/Correctness/Trees", "RustCrypto/Verification/Model", "RustCrypto/Verification/Index", "RustCrypto/Verification/Compare", "RustCrypto/Verification/Api", "RustCrypto/Verification/Decoded", "RustCrypto/Verification/Root/Model",
                   "RustCrypto/Signing/Full/Wots", "RustCrypto/Signing/Full/Path", "RustCrypto/Signing/Full/Constants", "RustCrypto/Signing/Full/Model", "RustCrypto/Signing/Full/Buffer", "RustCrypto/Signing/Full/Failure", "RustCrypto/Signing/Full/SelectPath", "RustCrypto/Signing/Full/Success", "RustCrypto/Signing/Full/Loop", "RustCrypto/Signing/Full/Native", "RustCrypto/Signing/Full/Index", "RustCrypto/Signing/Full/Public", "RustCrypto/Signing/Full/Core", "RustCrypto/Correctness/Wots", "RustCrypto/Correctness/PublicKey", "RustCrypto/Correctness/Signing/Serialization", "RustCrypto/Correctness/Signing/Core", "RustCrypto/Correctness/Signing/Success", "RustCrypto/Correctness/Signing/Api",
                   *variant_proofs, "RustCrypto/Audit/Source"]
        checked_sources = {p.relative_to(folder).as_posix(): digest(p) for p in folder.rglob("*.lean")}
        for module in modules:
            checked(["lean", "-R", folder, "-DwarningAsError=true", folder / (module + ".lean"),
                     "-o", folder / (module + ".olean")], runtime,
                    logs / (module.replace("/", "-") + ".log"), env)
        if label == "sse2":
            raw = inputs["Funs.lean"].decode("utf-8")
            body = raw.split("def signature.write_nodes_loop.body", 1)[1].split("/--", 1)[0]
            contract = proof_contents[ROOT / "formal/RustCrypto/Serialization/Writer.lean"].decode("utf-8")
            contract = "@[step] theorem body_success" + contract.split("@[step] theorem body_success", 1)[1].split("@[step] theorem body_done", 1)[0]
            contract = contract.replace("lean_sphincs.signature.write_nodes_loop.body", "lean_sphincs.Control.writer_body")
            positive = ("module\nimport LeanSphincs.Funs\nopen Aeneas Aeneas.Std Result ControlFlow\n"
                        "namespace lean_sphincs\ndef Control.writer_body" + body +
                        "\nend lean_sphincs\nnamespace WriterControl\n"
                        "abbrev Node := Aeneas.Std.Array U8 16#usize\n" + contract + "\nend WriterControl\n")
            control_file = logs / "positiveWriter.lean"
            control_file.write_text(positive, encoding="utf-8")
            checked(["lean", "-DwarningAsError=true", control_file], runtime, logs / "positiveWriter.log", env)
            site = "let i4 ← i + 1#usize"
            if positive.count(site) != 1:
                raise RuntimeError("writer mutation site changed")
            control_file = logs / "negativeWriter.lean"
            control_file.write_text(positive.replace(site, "let i4 ← i + 2#usize"), encoding="utf-8")
            def reject(path, expected, log):
                with log.open("w", encoding="utf-8") as stream:
                    failed = subprocess.run(["lean", "-DwarningAsError=true", str(path)], cwd=runtime,
                                            env=env, stdout=stream, stderr=subprocess.STDOUT)
                if failed.returncode == 0 or expected not in log.read_text(encoding="utf-8"):
                    raise RuntimeError("negative control did not fail as expected: " + str(log))
            reject(control_file, "unsolved goals", logs / "negativeWriter.log")
            audit = (folder / "RustCrypto/Audit/Source.lean").read_text(encoding="utf-8")
            injection = ("public axiom lean_sphincs.Control.bad : False\n"
                         "public theorem lean_sphincs.Control.rejected : False := lean_sphincs.Control.bad\n")
            control_file = logs / "negativeAssumption.lean"
            control_file.write_text(audit.replace("run_cmd do", injection + "run_cmd do"), encoding="utf-8")
            reject(control_file, "unexpected dependency lean_sphincs.Control.bad", logs / "negativeAssumption.log")
            required_site = "let required : List Name := ["
            if audit.count(required_site) != 1:
                raise RuntimeError("required-contract guard changed")
            control_file = logs / "negativeMissingContract.lean"
            control_file.write_text(audit.replace(required_site,
                required_site + "`lean_sphincs.Control.missing_contract,"), encoding="utf-8")
            reject(control_file, "required correctness theorem missing: lean_sphincs.Control.missing_contract",
                   logs / "negativeMissingContract.log")
            rotation_site = "let ux7 ← hash.batch.rotate 44#u32 ux6"
            if raw.count(rotation_site) != 1:
                raise RuntimeError("SIMD rotation mutation site changed")
            mutation_root = workspace / "negative-rho"
            shutil.copytree(folder / "LeanSphincs", mutation_root / "LeanSphincs", dirs_exist_ok=True)
            mutation_file = mutation_root / "LeanSphincs/Funs.lean"
            mutation_file.write_text(raw.replace(rotation_site,
                "let ux7 ← hash.batch.rotate 45#u32 ux6"), encoding="utf-8")
            mutation_env = env.copy()
            mutation_env["LEAN_PATH"] = str(mutation_root) + os.pathsep + env["LEAN_PATH"]
            checked(["lean", "-R", mutation_root, "-DwarningAsError=true", mutation_file,
                     "-o", mutation_root / "LeanSphincs/Funs.olean"], runtime,
                    logs / "negativeRho-valid-source.log", mutation_env)
            # Isolate the changed immediate call and give a closed, nonzero witness.
            # Rechecking the entire false round claim can spend its budget unfolding
            # symbolic word expressions; this control must fail on a concrete mismatch.
            def rotation_control(angle):
                return ("module\nimport LeanSphincs.Funs\nimport RustCrypto.Hash.Keccak.Rotate\n"
                        "open Aeneas Aeneas.Std Result\n"
                        f"example : lean_sphincs.hash.batch.rotate {angle}#u32 (fun _ => 1#u64) "
                        "⦃ out => (out 0).bv = (1#64).rotateLeft 44 ⦄ := by\n"
                        f"  apply WP.spec_mono (RustCrypto.SimdRound.rotate_spec {angle}#u32 "
                        "(fun _ => 1#u64) (by decide))\n"
                        "  intro out hout\n  exact hout 0\n")
            positive_angle = re.search(r"hash\.batch\.rotate (\d+)#u32 ux6", rotation_site).group(1)
            negative_angle = re.search(r"let ux7 ← hash\.batch\.rotate (\d+)#u32 ux6",
                                      mutation_file.read_text(encoding="utf-8")).group(1)
            positive_call = logs / "positiveRho.lean"
            positive_call.write_text(rotation_control(positive_angle), encoding="utf-8")
            checked(["lean", "-DwarningAsError=true", positive_call], runtime,
                    logs / "positiveRho.log", env)
            negative_call = logs / "negativeRho.lean"
            negative_call.write_text(rotation_control(negative_angle), encoding="utf-8")
            with (logs / "negativeRho.log").open("w", encoding="utf-8") as stream:
                failed = subprocess.run(["lean", "-DwarningAsError=true", str(negative_call)],
                    cwd=runtime, env=mutation_env, stdout=stream, stderr=subprocess.STDOUT)
            if failed.returncode == 0 or "type mismatch" not in (logs / "negativeRho.log").read_text(encoding="utf-8").lower():
                raise RuntimeError("wrong SIMD rotation was not rejected with the concrete witness")
            chi_site = "let ux ← Array.index_usize rotated 0#usize"
            if raw.count(chi_site) != 1:
                raise RuntimeError("SIMD chi mutation site changed")
            chi_root = workspace / "negative-chi"
            shutil.copytree(folder / "LeanSphincs", chi_root / "LeanSphincs", dirs_exist_ok=True)
            chi_file = chi_root / "LeanSphincs/Funs.lean"
            chi_file.write_text(raw.replace(chi_site,
                "let ux ← Array.index_usize rotated 1#usize"), encoding="utf-8")
            chi_env = env.copy()
            chi_env["LEAN_PATH"] = str(chi_root) + os.pathsep + env["LEAN_PATH"]
            checked(["lean", "-R", chi_root, "-DwarningAsError=true", chi_file,
                     "-o", chi_root / "LeanSphincs/Funs.olean"], runtime,
                    logs / "negativeChi-valid-source.log", chi_env)
            chi_contract = (folder / "RustCrypto/Hash/Keccak/Permutation.lean").read_text(encoding="utf-8")
            positive_chi = logs / "positiveChi.lean"
            positive_chi.write_text(chi_contract, encoding="utf-8")
            checked(["lean", "-DwarningAsError=true", positive_chi], runtime,
                    logs / "positiveChi.log", env)
            negative_chi = logs / "negativeChi.lean"
            negative_chi.write_text(chi_contract, encoding="utf-8")
            chi_log = logs / "negativeChi.log"
            with chi_log.open("w", encoding="utf-8") as stream:
                failed = subprocess.run(["lean", "-DwarningAsError=true", str(negative_chi)],
                    cwd=runtime, env=chi_env, stdout=stream, stderr=subprocess.STDOUT)
            chi_diagnostic = chi_log.read_text(encoding="utf-8").lower()
            if failed.returncode == 0 or not any(marker in chi_diagnostic for marker in
                    ["unsolved goals", "type mismatch", "tactic `rfl` failed", "tactic 'rfl' failed"]):
                raise RuntimeError("wrong SIMD chi index was not rejected by its source contract")
            controls = {"unchanged_source_iteration": "accepted", "skipped_node_iteration": "rejected",
                        "injected_assumption": "rejected", "missing_required_contract": "rejected",
                        "unchanged_simd_round": "accepted",
                        "incorrect_simd_rotation": "rejected with concrete lane witness",
                        "rho_control_scope": "immediate call extracted from mutated source round",
                        "unchanged_chi_contract": "accepted",
                        "incorrect_chi_lane_index": "rejected by rechecked source contract",
                        "chi_control_scope": "full permutation proof against typed mutated chi body"}
        if body_hashes != {name: hashlib.sha256((folder / "LeanSphincs" / name).read_bytes()).hexdigest() for name in body_hashes}:
            raise RuntimeError("generated body changed during checking: " + label)
        if checked_sources != {p.relative_to(folder).as_posix(): digest(p) for p in folder.rglob("*.lean")}:
            raise RuntimeError("worker proof sources changed during checking: " + label)
        item = {"variant": label, "local_functions": len(local), "kernel_checked": True,
                         "generated_bodies": body_hashes, "variant_proofs": variant_proofs,
                         "audit_source_sha256": digest(folder / "RustCrypto/Audit/Source.lean"),
                         "checked_sources": checked_sources,
                         "variant_proof_sha256": {module: digest(folder / (module + ".lean"))
                                                   for module in variant_proofs}}
        print(label + ": complete source contracts and dependency audit checked", flush=True)
        return item, controls

    executor = ThreadPoolExecutor(max_workers=args.jobs)
    try:
        checked_variants = list(executor.map(check_variant, variants))
    finally:
        executor.shutdown(wait=True, cancel_futures=True)
    evidence = [item for item, _ in checked_variants]
    controls = {key: value for _, control in checked_variants for key, value in control.items()}
    if report_sha256 != hashlib.sha256((translated / "report.json").read_bytes()).hexdigest() or translation.load_translation(translated) != report:
        raise RuntimeError("translation provenance changed during checking")
    if pipeline_before != {p.relative_to(ROOT).as_posix(): digest(p) for p in pipeline_files}:
        raise RuntimeError("verification pipeline changed during checking")
    reference.prepare(offline=True)
    if stdlib_model != runtime_models.validate_stdlib_model(runtime, backend):
        raise RuntimeError("standard-library model changed during checking")
    current_files = [ROOT / "formal/Batching/Keccak.lean", ROOT / "formal/Batching/Constants.lean",
                     *sorted((ROOT / "formal/Runtime").rglob("*.lean")),
                     *sorted((ROOT / "formal/RustCrypto").rglob("*.lean"))]
    if snapshot != extraction.source_snapshot() or before != {p.relative_to(ROOT).as_posix(): digest(p) for p in current_files}:
        raise RuntimeError("source or proof files changed during checking")
    result = {"scope": "complete deterministic source functional refinement: key generation, bounded/default signing, decoding/public verification, successful-signature roundtrip, all production scalar/SIMD paths, and observable SignError methods under the documented standard-library/external models", "full_crate_formally_verified": True,
              "source_functional_refinement_complete": True,
              "sources": snapshot, "proof_sources": before, "toolchain": pin,
              "stdlib_model": stdlib_model, "pipeline_sources": pipeline_before,
              "trust_boundary": ["Lean kernel and standard foundations", "pinned Charon/Aeneas translation", "documented Rust standard-library, Alloy Keccak and wide word interface models"],
              "not_proved": ["cryptographic hardness", "hash-query trace equivalence", "constant time or side channels", "Rust compiler, external dependency machine code or CPU correctness"],
              "translation_report_sha256": report_sha256, "variants": evidence, "controls": controls}
    (output / "evidence.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(output / "evidence.json", flush=True)


if __name__ == "__main__":
    main()
