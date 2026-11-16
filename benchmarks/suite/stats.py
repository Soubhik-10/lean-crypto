"""Analysis of raw batch averages; no outliers are discarded."""
from __future__ import annotations
import math
import random
import statistics


def percentile(values, fraction):
    ordered = sorted(values)
    if not ordered:
        raise ValueError("Empty sample set")
    at = (len(ordered) - 1) * fraction
    lo, hi = math.floor(at), math.ceil(at)
    return ordered[lo] + (ordered[hi] - ordered[lo]) * (at - lo)


def validate(report, samples):
    if report.get("schema_version") != 1 or report.get("status") != "complete":
        raise ValueError("Incomplete or unsupported report")
    names = set()
    for measurement in report["measurements"]:
        if measurement["name"] in names:
            raise ValueError("Duplicate measurement")
        names.add(measurement["name"])
        raw = measurement["samples"]
        if len(raw) != samples or [r["index"] for r in raw] != list(range(samples)):
            raise ValueError("Missing or reordered samples")
        for row in raw:
            if row["work_items"] <= 0 or row["elapsed_ns"] <= 0:
                raise ValueError("Invalid timing denominator")
            expected = row["elapsed_ns"] / row["work_items"]
            if not math.isclose(expected, row["ns_per_op"], rel_tol=1e-12):
                raise ValueError("Raw time and ns/op disagree")


def summarize(passes, *, resamples=2000, block=10, seed=20261115):
    if not passes or any(not values for values in passes):
        raise ValueError("Each pass must contain samples")
    raw = [x for values in passes for x in values]
    if any(not math.isfinite(x) or x <= 0 for x in raw):
        raise ValueError("Timings must be positive and finite")
    rng = random.Random(seed)
    boot = []
    # Resample consecutive blocks within each pass to retain some local correlation.
    for _ in range(resamples):
        draw = []
        for values in passes:
            sampled = []
            while len(sampled) < len(values):
                start = rng.randrange(len(values))
                sampled.extend(values[(start + i) % len(values)] for i in range(block))
            draw.extend(sampled[:len(values)])
        boot.append(statistics.median(draw))
    median = statistics.median(raw)
    return {
        "samples": len(raw), "passes": len(passes), "median_ns": median,
        "p05_ns": percentile(raw, .05), "p95_ns": percentile(raw, .95),
        "p99_ns": percentile(raw, .99), "min_ns": min(raw), "max_ns": max(raw),
        "mean_ns": statistics.mean(raw), "stdev_ns": statistics.stdev(raw) if len(raw) > 1 else 0,
        "median_ci95_ns": [percentile(boot, .025), percentile(boot, .975)],
        "pass_medians_ns": [statistics.median(values) for values in passes],
        "bootstrap_resamples": resamples, "bootstrap_block_samples": block,
        "outliers_removed": 0, "pass_median_spread_percent": (max(statistics.median(v) for v in passes) / min(statistics.median(v) for v in passes) - 1) * 100,
        "unit": "batch-average ns per operation; batch hashes normalized per input",
    }


def display(ns):
    if ns >= 1_000_000:
        return f"{ns / 1_000_000:.3f} ms"
    if ns >= 1_000:
        return f"{ns / 1_000:.3f} us"
    return f"{ns:.2f} ns"
