"""Compact README tables; complete metadata and secondary cases remain in JSON."""
from __future__ import annotations
import json

from . import stats

TARGETS = {"baseline": "SSE2", "v2": "SSE4.2", "v3": "AVX2", "v4": "AVX-512", "native": "native"}
BACKENDS = {"portable": "RustCrypto", "tiny": "tiny-keccak", "assembly": "asm-keccak"}


def load_measurements(path, *, resamples=2000):
    """Recompute summaries from the published batch times, without executing Rust."""
    data = json.loads(path.read_text(encoding="utf-8"))
    sampling = data["sampling"]
    version = data.get("schema_version")
    if version not in (1, 2) or (version == 1 and sampling["passes"] != 1):
        raise ValueError("Unsupported published measurement format")
    if sampling["outliers_removed"] != 0:
        raise ValueError("Published measurements must retain all samples")
    summaries, seen = [], set()
    for measurement in data["measurements"]:
        configuration, name = measurement["configuration"], measurement["operation"]
        if configuration not in data["configurations"] or (configuration, name) in seen:
            raise ValueError("Unknown configuration or duplicate measurement")
        seen.add((configuration, name))
        recorded = [measurement] if version == 1 else measurement["passes"]
        if len(recorded) != sampling["passes"]:
            raise ValueError("Missing measurement pass")
        passes = []
        for batch in recorded:
            iterations = batch["iterations"]
            items = batch["work_items_per_iteration"]
            elapsed = batch["elapsed_ns"]
            if (len(elapsed) != sampling["samples_per_case"] or
                    any(type(value) is not int or value <= 0 for value in [iterations, items, *elapsed])):
                raise ValueError("Invalid sample count, elapsed time or timing denominator")
            passes.append([value / (iterations * items) for value in elapsed])
        summary = stats.summarize(passes, resamples=resamples)
        summaries.append({"configuration": configuration, "name": name, **summary})
    state = {"machine": {"processors": [data["cpu"]]},
             "plan": {"profile": {"samples": sampling["samples_per_case"], "passes": sampling["passes"]}},
             "builds": {"rustc": data["rustc"], "jobs": data["configurations"]},
             "reference_revision": data["reference_revision"]}
    return state, summaries


def selection(configuration, built):
    job = built.get("configuration", {})
    target = job.get("target", {}).get("id", configuration.split("-", 1)[0])
    backend = job.get("keccak")
    if backend is None:
        backend = next((name for name in BACKENDS if f"-{name}-" in configuration), None)
    recovery = job.get("ecrecover")
    if recovery is None:
        recovery = next((name for name in ("libsecp256k1", "k256") if name in configuration), None)
    return target, backend, recovery


def render_batched(lines, state, summaries, *, include_reference):
    """Keep compiler variants distinct instead of folding them into one cell."""
    jobs = state["builds"]["jobs"]
    values = {}
    for row in summaries:
        key = (row["configuration"], row["name"])
        if key in values:
            raise ValueError("Duplicate measurement")
        values[key] = row["median_ns"]

    def build_cells(configuration):
        built = jobs[configuration]
        target, backend, _ = selection(configuration, built)
        flags = built.get("rustflags", built.get("configuration", {}).get("extra_rustflags", []))
        slp = "disabled" if "no-vectorize-slp" in flags else "enabled"
        return [TARGETS[target], BACKENDS[backend], slp]

    def cell(configuration, name, divisor):
        value = values.get((configuration, name))
        return "—" if value is None else f"{value / divisor:.2f}"

    for operation, heading, unit, divisor in [("verify_wire", "Verification", "µs", 1000),
                                              ("sign", "Signing", "ms", 1000000),
                                              ("key_gen", "Key generation", "ms", 1000000)]:
        own_name = f"macro/native/{operation}/mixed"
        matching = [configuration for configuration in jobs if (configuration, own_name) in values]
        if not matching:
            continue
        header = ["Compiler target", "lean-sphincs Keccak", "LLVM SLP", f"lean-sphincs ({unit})"]
        if include_reference:
            header += [f"leanVM (unmodified, pinned revision) ({unit})",
                       f"leanVM + local SIMD batching adapter ({unit})", "Adapter speedup"]
        lines += [f"### {heading}", "", "| " + " | ".join(header) + " |",
                  "| --- | --- | --- | " + " | ".join(["---:"] * (len(header) - 3)) + " |"]
        for configuration in matching:
            cells = build_cells(configuration) + [cell(configuration, own_name, divisor)]
            if include_reference:
                batched_name = f"macro/batched/{operation}/mixed"
                comparison = values.get((configuration, batched_name))
                faster = "—" if comparison is None else f"{(values[(configuration, own_name)] / comparison - 1) * 100:+.1f}%"
                cells += [cell(configuration, f"macro/reference/{operation}/mixed", divisor),
                          cell(configuration, batched_name, divisor), faster]
            lines.append("| " + " | ".join(cells) + " |")
        lines.append("")
    return "\n".join(lines)


def render(state, summaries, *, include_reference=True):
    machine = state["machine"]
    cpu = (machine.get("processors") or [{}])[0]
    model = cpu.get("Name", machine.get("model_name", "CPU not reported")).strip()
    hardware = f"CPU: {model}"
    if cpu.get("NumberOfCores") and cpu.get("NumberOfLogicalProcessors"):
        hardware += f" ({cpu['NumberOfCores']} cores, {cpu['NumberOfLogicalProcessors']} threads)"
    hardware += "."
    compiler = state["builds"]["rustc"].splitlines()
    llvm = next((line for line in compiler if line.startswith("LLVM version:")), "")
    compiler_version = compiler[0].split()[1]
    compiler_text = "Rust " + compiler_version + ("; LLVM " + llvm.split(":", 1)[1].strip() if llvm else "")
    lines = ["## Native benchmark results", "", hardware, "",
             f"Compiler: {compiler_text}. Optimization level 3, Thin LTO, one codegen unit.", ""]
    profile = state["plan"]["profile"]
    batched = any(row["name"].startswith("macro/batched/") for row in summaries)
    caption = (f"Median time per operation from {profile['samples'] * profile['passes']} samples "
               f"per configuration ({profile['passes']} pass{'es' if profile['passes'] != 1 else ''}).")
    if include_reference:
        if batched:
            caption += " Adapter speedup = `(lean-sphincs / batched adapter - 1) × 100%`; negative values mean the adapter is slower."
        else:
            caption += " Measured speedup = `(leanVM / lean-sphincs - 1) × 100%`; negative values mean slower."
    lines += [caption, ""]
    if include_reference:
        lines += ["Verification starts from encoded signatures; signing and key generation include serialization. "
                  "Small differences need confirmation across repeat runs.", "",
                  "The Keccak column selects lean-sphincs' Alloy backend. Verification also uses paired "
                  "SSE2 FORS hashing in SSE2 and SSE4.2 builds. leanVM uses its own CPU-selected scalar "
                  "and SIMD paths. Compiler flags apply to both implementations within each row. "
                  "See the [measurement method and raw data]"
                  "(benchmarks/SUITE.md#published-measurements).", ""]
        revision = state.get("reference_revision")
        if revision:
            lines += [f"leanVM: [native Rust leanSPHINCS implementation]"
                      f"(https://github.com/leanEthereum/leanVM/tree/{revision}/crates/lean_sphincs).", ""]
        if batched:
            lines += ["The batched column is a local experimental adapter over leanVM's public internals. "
                      "It uses leanVM's SIMD hash API within one signature operation and is not stock leanVM.", ""]
    if batched:
        return render_batched(lines, state, summaries, include_reference=include_reference)
    selected = {name: selection(name, item) for name, item in state["builds"]["jobs"].items()}
    values = {}
    for row in summaries:
        target, backend, recovery = selected[row["configuration"]]
        key = (target, backend, recovery, row["name"])
        if key in values:
            raise ValueError("Multiple builds for one table cell; report separate sessions")
        values[key] = row["median_ns"]

    def cell(target, backend, recovery, operation, divisor):
        value = values.get((target, backend, recovery, operation))
        return "—" if value is None else f"{value / divisor:.2f}"

    for operation, heading, unit, divisor in [("verify_wire", "Verification", "µs", 1_000),
                                              ("sign", "Signing", "ms", 1_000_000),
                                              ("key_gen", "Key generation", "ms", 1_000_000)]:
        matching = [(target, backend) for target in TARGETS for backend in BACKENDS
                    if (target, backend, "libsecp256k1", f"macro/native/{operation}/mixed") in values]
        if not matching:
            continue
        lines += [f"### {heading}", ""]
        header = f"| Compiler target | lean-sphincs Keccak | lean-sphincs ({unit}) |"
        separator = "| --- | --- | ---: |"
        if include_reference:
            header += f" leanVM (unmodified, pinned revision) ({unit}) | Measured speedup |"
            separator += " ---: | ---: |"
        lines += [header, separator]
        for target, backend in matching:
            own = cell(target, backend, "libsecp256k1", f"macro/native/{operation}/mixed", divisor)
            row = f"| {TARGETS[target]} | {BACKENDS[backend]} | {own} |"
            if include_reference:
                reference = values.get((target, backend, "libsecp256k1", f"macro/reference/{operation}/mixed"))
                native = values[(target, backend, "libsecp256k1", f"macro/native/{operation}/mixed")]
                faster = "—" if reference is None else f"{(reference / native - 1) * 100:+.1f}%"
                row += " " + cell(target, backend, "libsecp256k1", f"macro/reference/{operation}/mixed", divisor) + " |"
                row += f" {faster} |"
            lines.append(row)
        lines.append("")

    if any(key[3] == "macro/evm2/ecrecover" for key in values):
        lines += ["### Ecrecover", ""]
        for recovery, heading in [("libsecp256k1", "libsecp256k1"), ("k256", "k256")]:
            targets = [target for target in TARGETS
                       if any((target, backend, recovery, "macro/evm2/ecrecover") in values for backend in BACKENDS)]
            if not targets:
                continue
            lines += [f"#### evm2 {heading}", "",
                      "| Compiler target | RustCrypto (µs) | tiny-keccak (µs) | asm-keccak (µs) |",
                      "| --- | ---: | ---: | ---: |"]
            for target in targets:
                cells = [cell(target, backend, recovery, "macro/evm2/ecrecover", 1_000) for backend in BACKENDS]
                lines.append("| " + " | ".join([TARGETS[target], *cells]) + " |")
            lines.append("")
    return "\n".join(lines)
