"""Machine capture and gated child execution; no power settings are changed."""
from __future__ import annotations
from contextlib import contextmanager
import bisect
import ctypes
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def command(args, *, cwd=ROOT, env=None):
    result = subprocess.run(
        [str(x) for x in args], cwd=cwd, env=env, text=True, encoding="utf-8",
        errors="replace", capture_output=True, timeout=180,
        creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0,
    )
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}): {args}\n{result.stderr}")
    return result.stdout.strip()


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def powershell():
    result = shutil.which("pwsh") or shutil.which("powershell")
    if not result:
        raise RuntimeError("PowerShell is required for Windows machine capture")
    return result


def probe(toolchain):
    folder = ROOT / "benchmarks" / "build" / "probe"
    folder.mkdir(parents=True, exist_ok=True)
    binary = folder / ("host-probe.exe" if os.name == "nt" else "host-probe")
    command(["rustc", f"+{toolchain}", "--edition", "2024", HERE / "host_probe.rs", "-o", binary])
    return json.loads(command([binary]))


def snapshot(cpu):
    if os.name == "nt":
        return json.loads(command([powershell(), "-NoProfile", "-ExecutionPolicy", "Bypass",
                                   "-File", HERE / "machine.ps1", "-Cpu", cpu]))
    data = {"captured_utc": utc(), "platform": platform.platform(), "logical_cpu": cpu}
    for label, path in [("cpuinfo", "/proc/cpuinfo"), ("meminfo", "/proc/meminfo")]:
        if Path(path).exists():
            data[label] = Path(path).read_text()
    info = data.get("cpuinfo", "")
    data["model_name"] = next((line.split(":", 1)[1].strip() for line in info.splitlines()
                               if line.startswith("model name")), platform.processor())
    for label in ["scaling_governor", "scaling_min_freq", "scaling_max_freq",
                  "cpuinfo_min_freq", "cpuinfo_max_freq"]:
        path = Path(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/{label}")
        data[label] = path.read_text().strip() if path.exists() else None
    data["frequency_note"] = "OS-reported frequencies are not hardware effective clocks."
    return data


def require_same_machine(initial, current):
    keys = ("power_scheme", "processor_power_policy", "bios_version", "os_build",
            "ac_line_status", "model_name", "platform", "scaling_governor",
            "scaling_min_freq", "scaling_max_freq")
    for key in keys:
        if initial.get(key) != current.get(key):
            raise ValueError(f"Machine condition changed: {key}; create a new session")

    def processors(value):
        stable = ("Name", "Manufacturer", "NumberOfCores", "NumberOfLogicalProcessors",
                  "MaxClockSpeed", "L2CacheSize", "L3CacheSize")
        return [{key: cpu.get(key) for key in stable} for cpu in value.get("processors", [])]
    if processors(initial) != processors(current):
        raise ValueError("Processor configuration changed; create a new session")


def affinity(process, cpu):
    if cpu < 0:
        raise ValueError("CPU index must be nonnegative")
    if os.name == "nt":
        if cpu >= 64:
            raise ValueError("This runner uses processor group 0; CPU must be below 64")
        kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        kernel.SetProcessAffinityMask.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
        kernel.GetProcessAffinityMask.argtypes = [
            ctypes.c_void_p, ctypes.POINTER(ctypes.c_size_t), ctypes.POINTER(ctypes.c_size_t)]
        handle = ctypes.c_void_p(int(process._handle))
        if not kernel.SetProcessAffinityMask(handle, 1 << cpu):
            raise ctypes.WinError(ctypes.get_last_error())
        actual, system = ctypes.c_size_t(), ctypes.c_size_t()
        if not kernel.GetProcessAffinityMask(handle, ctypes.byref(actual), ctypes.byref(system)):
            raise ctypes.WinError(ctypes.get_last_error())
        if actual.value != 1 << cpu:
            raise RuntimeError("Affinity verification failed")
        return {"mask": hex(actual.value), "group": 0, "logical_cpu": cpu}
    if not hasattr(os, "sched_setaffinity"):
        raise RuntimeError("Verified affinity is supported on Windows and Linux")
    os.sched_setaffinity(process.pid, {cpu})
    if os.sched_getaffinity(process.pid) != {cpu}:
        raise RuntimeError("Affinity verification failed")
    return {"logical_cpu": cpu}


def run_gated(args, *, cwd, env, cpu, stem, monitor=True):
    """The child waits on stdin until its affinity has been applied and checked."""
    stem = Path(stem)
    start = utc()
    stop = stem.with_suffix(".monitor-stop")
    if stop.exists():
        stop.unlink()
    monitor_process = None
    with stem.with_suffix(".stdout.log").open("w", encoding="utf-8") as out, \
         stem.with_suffix(".stderr.log").open("w", encoding="utf-8") as err:
        process = subprocess.Popen(
            [str(x) for x in args], cwd=cwd, env=env, stdin=subprocess.PIPE,
            stdout=out, stderr=err, text=True, encoding="utf-8",
            creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0,
        )
        try:
            applied = affinity(process, cpu)
            if monitor and os.name == "nt":
                monitor_process = subprocess.Popen(
                    [powershell(), "-NoProfile", "-ExecutionPolicy", "Bypass", "-File",
                     str(HERE / "machine.ps1"), "-Action", "Monitor", "-Cpu", str(cpu),
                     "-ProcessId", str(process.pid), "-OutputPath",
                     str(stem.with_suffix(".telemetry.jsonl")), "-StopFile", str(stop)],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                    creationflags=subprocess.CREATE_NO_WINDOW,
                )
                # The monitor uses another logical CPU when one is available.
                available = os.cpu_count() or 1
                if available > 1:
                    affinity(monitor_process, 0 if cpu != 0 else 1)
            process.stdin.write("start\n")
            process.stdin.flush()
            process.stdin.close()
            last_heartbeat = time.monotonic()
            while process.poll() is None:
                time.sleep(1)
                if time.monotonic() - last_heartbeat >= 30:
                    print(f"Running {stem.name}; progress: {stem.with_suffix('.stderr.log')}", flush=True)
                    last_heartbeat = time.monotonic()
            result = {"started_utc": start, "finished_utc": utc(),
                      "exit_code": process.returncode, "affinity": applied}
            if process.returncode:
                raise RuntimeError(f"Benchmark exited {process.returncode}; inspect {stem}")
            return result
        except BaseException:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            raise
        finally:
            stop.touch()
            if monitor_process:
                try:
                    monitor_process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    monitor_process.terminate()
                    monitor_process.wait(timeout=10)


def telemetry_summary(paths, reports):
    intervals = sorted((sample["started_unix_ns"], sample["started_unix_ns"] + sample["elapsed_ns"])
                       for report in reports for case in report["measurements"]
                       for sample in case["samples"] if "started_unix_ns" in sample)
    starts = [start for start, _ in intervals]
    frequencies, errors = [], []
    for path in paths:
        if not Path(path).exists():
            errors.append(f"Missing telemetry: {Path(path).name}")
            continue
        for line in Path(path).read_text(encoding="utf-8-sig").splitlines():
            try:
                row = json.loads(line)
                stamp = int(dt.datetime.fromisoformat(row["utc"].replace("Z", "+00:00")).timestamp() * 1e9)
                at = bisect.bisect_right(starts, stamp) - 1
                during = at >= 0 and stamp <= intervals[at][1]
                value = row.get("reported_frequency_mhz")
                if during and isinstance(value, (float, int)) and value > 0:
                    frequencies.append(value)
                if row.get("counter_error"):
                    errors.append(row["counter_error"])
            except (ValueError, KeyError):
                errors.append(f"Malformed telemetry line in {Path(path).name}")
    return {
        "source": "OS-reported per-CPU performance counters during timed batches",
        "effective_hardware_clock": False, "observations": len(frequencies),
        "median_reported_mhz": statistics.median(frequencies) if frequencies else None,
        "min_reported_mhz": min(frequencies) if frequencies else None,
        "max_reported_mhz": max(frequencies) if frequencies else None,
        "errors": sorted(set(errors)),
    }


def archive_attempt(session, task):
    """Retain an interrupted/invalid attempt before retrying its task name."""
    session = Path(session).resolve()
    files = [path for path in session.glob(task + ".*") if path.is_file()]
    if not files:
        return None
    destination = session / "attempts" / f"{task}-{time.time_ns()}"
    destination.mkdir(parents=True)
    if not destination.resolve().is_relative_to(session):
        raise ValueError("Attempt archive escapes session")
    for path in files:
        if path.resolve().parent != session:
            raise ValueError("Unexpected attempt path")
        path.rename(destination / path.name)
    return str(destination.relative_to(session))


@contextmanager
def cpu_lock(cpu):
    """Prevent cooperating runners from measuring concurrently on the same CPU."""
    if os.name == "nt":
        kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        kernel.CreateMutexW.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_wchar_p]
        kernel.CreateMutexW.restype = ctypes.c_void_p
        kernel.WaitForSingleObject.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
        kernel.ReleaseMutex.argtypes = [ctypes.c_void_p]
        kernel.CloseHandle.argtypes = [ctypes.c_void_p]
        handle = kernel.CreateMutexW(None, False, f"Local\\LeanSphincsBenchmarkGroup0Cpu{cpu}")
        if not handle:
            raise ctypes.WinError(ctypes.get_last_error())
        acquired = kernel.WaitForSingleObject(handle, 0) in (0, 0x80)
        if not acquired:
            kernel.CloseHandle(handle)
            raise RuntimeError(f"Another benchmark runner owns logical CPU {cpu}")
        try:
            yield
        finally:
            kernel.ReleaseMutex(handle)
            kernel.CloseHandle(handle)
    else:
        import fcntl
        folder = ROOT / "benchmarks/build"
        folder.mkdir(parents=True, exist_ok=True)
        with (folder / f"cpu-{cpu}.lock").open("a+b") as stream:
            try:
                fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise RuntimeError(f"Another benchmark runner owns CPU {cpu}") from error
            try:
                yield
            finally:
                fcntl.flock(stream, fcntl.LOCK_UN)
