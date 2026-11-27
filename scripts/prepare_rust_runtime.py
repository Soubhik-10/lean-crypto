#!/usr/bin/env python3
"""Prepare pinned Aeneas/Mathlib source archives and their Lean cache without Git clones.

Use Linux/WSL with the Lean toolchain from formal/extractor.json on PATH.
Aeneas and Charon executables are built/installed separately at that pin.
"""
import argparse
import hashlib
import re
import json
import os
import shutil
import subprocess
import tarfile
import urllib.request
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

STDLIB_MODELS = frozenset([
    "Aeneas/Std/Core/FmtModel.lean", "Aeneas/Std/Core/Fmt.lean",
    "Aeneas/Std/Scalar/Display.lean", "Aeneas/Std/Scalar/Fmt.lean",
])
IMPORT = re.compile(r"^(?:public )?(?:meta )?import (?:all )?([\w.]+)", re.MULTILINE)


def lean_hashes(root):
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in root.rglob("*.lean") if ".lake" not in p.relative_to(root).parts}


def mathlib_imports(source):
    paths = [*source.rglob("*.lean"), *(ROOT / "formal/RustCrypto").rglob("*.lean"),
             *(ROOT / "formal/Runtime").rglob("*.lean")]
    return sorted({module for path in paths if ".lake" not in path.parts
                   for module in IMPORT.findall(path.read_text(encoding="utf-8"))
                   if module.startswith("Mathlib.")})


def stdlib_manifest(stock):
    model = ROOT / "formal/Runtime"
    files = lean_hashes(model)
    if set(files) != STDLIB_MODELS:
        raise RuntimeError("standard-library model file allowlist changed")
    expected = lean_hashes(stock)
    expected.update(files)
    return {"files": files, "expected_sources": expected}


def validate_stdlib_model(runtime, stock):
    expected = stdlib_manifest(stock)
    target = runtime / "stdlib-model"
    if lean_hashes(target) != expected["expected_sources"]:
        raise RuntimeError("standard-library model differs from stock plus explicit interface models")
    saved = json.loads((target / "model-manifest.json").read_text(encoding="utf-8"))
    if saved["files"] != expected["files"] or saved["expected_sources"] != expected["expected_sources"]:
        raise RuntimeError("standard-library model provenance is stale")
    return saved


def prepare_stdlib_model(runtime, stock):
    """Keep stock sources intact and rebuild every importer of an interface model."""
    target = runtime / "stdlib-model"
    lib = target / ".lake/build/lib/lean"
    expected = stdlib_manifest(stock)
    if lean_hashes(runtime / "packages/aeneas") != lean_hashes(stock):
        raise RuntimeError("stock Aeneas runtime source changed")
    shutil.copytree(stock, target, dirs_exist_ok=True, ignore=shutil.ignore_patterns(".lake", ".git"))
    shutil.copytree(runtime / "packages/aeneas/.lake/build/lib/lean", lib, dirs_exist_ok=True)
    for relative in STDLIB_MODELS:
        dest = target / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / "formal/Runtime" / relative, dest)
    if lean_hashes(target) != expected["expected_sources"]:
        raise RuntimeError("unexpected standard-library model source")
    modules = {p.relative_to(target).with_suffix("").as_posix().replace("/", "."): p
               for p in target.rglob("*.lean") if ".lake" not in p.relative_to(target).parts}
    deps = {module: IMPORT.findall(path.read_text(encoding="utf-8")) for module, path in modules.items()}
    affected = {name.removesuffix(".lean").replace("/", ".") for name in STDLIB_MODELS}
    while True:
        expanded = affected | {module for module, imports in deps.items() if affected.intersection(imports)}
        if expanded == affected:
            break
        affected = expanded
    needed = set()
    def need(module):
        if module in needed:
            return
        needed.add(module)
        for dependency in deps[module]:
            if dependency in deps:
                need(dependency)
    need("Aeneas")
    affected &= needed
    order = []
    def visit(module):
        if module in order:
            return
        for dependency in deps[module]:
            if dependency in affected:
                visit(dependency)
        order.append(module)
    for module in sorted(affected):
        visit(module)
    env = os.environ.copy()
    paths = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=runtime, text=True).strip().split(os.pathsep)
    paths = [str((runtime / path).resolve()) if not Path(path).is_absolute() else path for path in paths]
    stock_lib = str(runtime / "packages/aeneas/.lake/build/lib/lean")
    if stock_lib not in paths:
        raise RuntimeError("stock runtime library is missing from Lean search path")
    env["LEAN_PATH"] = os.pathsep.join([str(lib) if path == stock_lib else path for path in paths])
    with (target / "rebuild.log").open("w", encoding="utf-8") as output:
        for module in order:
            path = modules[module]
            dest = lib / path.relative_to(target).with_suffix(".olean")
            dest.parent.mkdir(parents=True, exist_ok=True)
            strict = ["-DwarningAsError=true"] if path.relative_to(target).as_posix() in STDLIB_MODELS else []
            print("Checking standard-library model:", module, flush=True)
            subprocess.run(["lean", "-R", target, "-Dweak.linter.dupNamespace=false", *strict,
                            path, "-o", dest], cwd=target, env=env, stdout=output,
                           stderr=subprocess.STDOUT, check=True)
    expected["rebuilt_modules"] = order
    (target / "model-manifest.json").write_text(json.dumps(expected, indent=2) + "\n", encoding="utf-8")
    validate_stdlib_model(runtime, stock)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", required=True, type=Path, help="Tool cache, preferably on native Linux storage")
    parser.add_argument("--stdlib-model", action="store_true", help="Build the explicit observable-formatting standard-library model")
    parser.add_argument("--offline", action="store_true", help="Check existing sources without network/cache downloads")
    args = parser.parse_args()
    toolchain_pin = json.loads((ROOT / "formal/extractor.json").read_text(encoding="utf-8"))
    source = ROOT / "formal/.cache" / ("aeneas-" + toolchain_pin["aeneas"]["revision"]) / "backends/lean"
    if not source.is_dir():
        raise RuntimeError("Install the pinned Aeneas source archive in " + str(source.parent.parent))
    if (source / "lean-toolchain").read_text().strip() != toolchain_pin["lean_toolchain"]:
        raise RuntimeError("Aeneas source toolchain mismatch")
    root = args.runtime.resolve()
    root.mkdir(parents=True,exist_ok=True)
    packages=root/'packages'
    packages.mkdir(exist_ok=True)
    pin=json.loads((source/'lake-manifest.json').read_text())
    expected_identities = [{'name': p['name'], 'revision': p['rev'], 'url': p['url']} for p in pin['packages']]
    identities_path = root / 'source-pins.json'
    if identities_path.exists() and json.loads(identities_path.read_text(encoding='utf-8')) != expected_identities:
        raise RuntimeError('runtime dependency pins changed; use a fresh runtime directory')
    identities=[]
    for package in pin['packages']:
        name=package['name']
        dest=packages/name
        if not dest.resolve().is_relative_to(root) or not name.replace("-", "").replace("_", "").isalnum():
            raise RuntimeError("invalid dependency cache path")
        if not dest.exists():
            if args.offline:
                raise RuntimeError("missing offline dependency: " + name)
            repo=package['url'].removeprefix('https://github.com/').removesuffix('.git')
            url='https://codeload.github.com/'+repo+'/tar.gz/'+package['rev']
            archive=root/(name+'.tar.gz')
            if not archive.exists():
                with urllib.request.urlopen(url, timeout=60) as response:
                    archive.write_bytes(response.read())
            print('Preparing',name,flush=True)
            with tarfile.open(archive) as tar:
                members=tar.getmembers()
                prefix=members[0].name.split('/')[0]
                # Reject absolute and escaping paths before extracting the pinned archive.
                for member in members:
                    if member.name.startswith('/') or '..' in Path(member.name).parts:
                        raise RuntimeError('invalid archive path')
                staging=root/('unpack-'+name)
                staging.mkdir(exist_ok=True)
                tar.extractall(staging, filter='data')
                (staging/prefix).rename(dest)
        identities.append({'name':name,'revision':package['rev'],'url':package['url']})
    backend=packages/'aeneas'
    if not backend.exists(): shutil.copytree(source,backend,ignore=shutil.ignore_patterns('.lake'))
    (root/'lean-toolchain').write_text((source/'lean-toolchain').read_text())
    (root/'runtime-lakefile.toml').write_text('name = "sphincs_rust_runtime"\nversion = "0.1.0"\n[[require]]\nname = "aeneas"\npath = "packages/aeneas"\n')
    if not (root/'lakefile.toml').exists():
        shutil.copyfile(root/'runtime-lakefile.toml', root/'lakefile.toml')
    manifest={'version':'1.3.0','packagesDir':'.lake/packages','packages':[
        {'type':'path','name':p['name'],'dir':str(packages/p['name']),'inherited':True,
         'configFile':p['configFile'],'manifestFile':p['manifestFile']} for p in pin['packages']
    ]+[{'type':'path','name':'aeneas','dir':str(backend),'inherited':False,'configFile':'lakefile.lean','manifestFile':'lake-manifest.json'}]}
    (root/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    (root/'source-pins.json').write_text(json.dumps(identities,indent=2)+'\n')
    print(root,flush=True)

    if not args.offline:
        env = os.environ.copy()
        env["CI"] = "true"
        with (root / "prepare.log").open("w", encoding="utf-8") as log:
            subprocess.run(["lake", "exe", "cache", "--help"], cwd=root, env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
            links = packages / "mathlib/.lake/packages"
            links.mkdir(parents=True, exist_ok=True)
            for package in pin["packages"]:
                if package["name"] == "mathlib":
                    continue
                link = links / package["name"]
                target = packages / package["name"]
                if not link.exists():
                    link.symlink_to(target, target_is_directory=True)
                elif link.resolve() != target.resolve():
                    raise RuntimeError("unexpected dependency link: " + str(link))
            # Mathlib's own unchanged manifest supplies the Git source identities
            # used by its cache. The workspace itself uses matching source archives.
            subprocess.run(["lake", "env", "bash", "-c",
                            "cd packages/mathlib && exec .lake/build/bin/cache get \"$@\"",
                            "stdlib-deps", *mathlib_imports(source)],
                           cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    print("Prepared pinned Rust-proof runtime.", flush=True)

    if args.stdlib_model:
        if not args.offline:
            subprocess.run(["lake", "build", "Aeneas"], cwd=root, check=True, env=env)
        prepare_stdlib_model(root, source)


if __name__ == "__main__":
    main()
