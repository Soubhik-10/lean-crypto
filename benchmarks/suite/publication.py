"""Compact README tables; complete metadata and secondary cases remain in JSON."""
from __future__ import annotations

TARGETS = {"baseline": "SSE2", "v2": "SSE4.2", "v3": "AVX2", "v4": "AVX-512", "native": "native"}
BACKENDS = {"portable": "RustCrypto", "tiny": "tiny-keccak", "assembly": "asm-keccak"}


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


def render(state, summaries, *, include_reference=True):
    machine = state["machine"]
    cpu = (machine.get("processors") or [{}])[0]
    model = cpu.get("Name", machine.get("model_name", "CPU not reported")).strip()
    hardware = f"CPU: {model}"
    if cpu.get("NumberOfCores") and cpu.get("NumberOfLogicalProcessors"):
        hardware += f" ({cpu['NumberOfCores']} cores, {cpu['NumberOfLogicalProcessors']} threads)"
    hardware += "."
    memory = machine.get("memory_bytes")
    if isinstance(memory, (int, float)):
        hardware += f" RAM: {memory / (1024 ** 3):.0f} GiB."
    compiler = state["builds"]["rustc"].splitlines()
    llvm = next((line for line in compiler if line.startswith("LLVM version:")), "")
    compiler_version = compiler[0].split()[1]
    compiler_text = "Rust " + compiler_version + ("; LLVM " + llvm.split(":", 1)[1].strip() if llvm else "")
    lines = ["## Native benchmark results", "", hardware, "",
             f"OS: {machine.get('os_caption', machine.get('platform', 'unreported'))}.", "",
             f"Compiler: {compiler_text}. Optimization level 3, Thin LTO, one codegen unit.", ""]
    profile = state["plan"]["profile"]
    lines += [f"Median time per operation from {profile['samples'] * profile['passes']} samples per configuration.", ""]
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
        header = f"| Compiler target | Hash backend | lean-sphincs ({unit}) |"
        separator = "| --- | --- | ---: |"
        if include_reference:
            header += f" leanVM ({unit}) |"
            separator += " ---: |"
        lines += [header, separator]
        for target, backend in matching:
            own = cell(target, backend, "libsecp256k1", f"macro/native/{operation}/mixed", divisor)
            row = f"| {TARGETS[target]} | {BACKENDS[backend]} | {own} |"
            if include_reference:
                row += " " + cell(target, backend, "libsecp256k1", f"macro/reference/{operation}/mixed", divisor) + " |"
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
