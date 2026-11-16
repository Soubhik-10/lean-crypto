"""Synthetic checks only: never starts a benchmark binary."""
import argparse
import importlib.util
from pathlib import Path
import unittest

import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from suite import stats, host

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("matrix_runner", ROOT / "benchmarks/run.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class AnalysisTests(unittest.TestCase):
    def test_constant_samples_have_exact_confidence_interval(self):
        result = stats.summarize([[100.0] * 20, [100.0] * 20], resamples=100)
        self.assertEqual(result["median_ci95_ns"], [100.0, 100.0])
        self.assertEqual(result["samples"], 40)

    def test_outlier_is_retained(self):
        result = stats.summarize([[100.0] * 99 + [1e9]], resamples=100)
        self.assertEqual(result["outliers_removed"], 0)
        self.assertEqual(result["max_ns"], 1e9)
        self.assertEqual(result["samples"], 100)

    def test_bootstrap_is_reproducible(self):
        data = [[float(i) for i in range(1, 50)]]
        self.assertEqual(stats.summarize(data, resamples=100), stats.summarize(data, resamples=100))

    def test_timing_denominator_and_sample_indices_are_validated(self):
        sample = {"index": 0, "iterations": 2, "work_items": 4,
                  "elapsed_ns": 100, "ns_per_op": 25.0}
        report = {"schema_version": 1, "status": "complete",
                  "measurements": [{"name": "test", "samples": [sample]}]}
        stats.validate(report, 1)
        sample["ns_per_op"] = 50.0
        with self.assertRaises(ValueError):
            stats.validate(report, 1)

    def test_unfinished_reports_cannot_be_published(self):
        with self.assertRaises(ValueError):
            stats.validate({"schema_version": 1, "status": "running"}, 500)


class PlanTests(unittest.TestCase):
    def options(self):
        return argparse.Namespace(profile="publication", samples=None, sample_ms=None,
                                  passes=None, groups=None, per_fixture=False, targets=None, cpu=2)

    def test_unsupported_isa_levels_are_skipped(self):
        import json
        config = json.loads(runner.CONFIG.read_text())
        result = runner.selected_plan(self.options(), config,
                                      {"architecture": "x86_64", "features": {"sse2": True}})
        self.assertEqual({j["target"]["id"] for j in result["jobs"]}, {"baseline", "native"})
        self.assertEqual(len(result["skipped"]), 3)
        self.assertGreater(result["minimum_sampling_hours"], 0)

    def test_unrecognized_group_fails_before_execution(self):
        import json
        options = self.options()
        options.groups = "typo"
        with self.assertRaises(ValueError):
            runner.selected_plan(options, json.loads(runner.CONFIG.read_text()),
                                 {"architecture": "x86_64", "features": {"sse2": True}})

    def test_vectorization_workaround_has_distinct_binary_identity(self):
        import json
        options = self.options()
        options.targets = "native"
        options.hashing = "tiny"
        options.recovery = "libsecp256k1"
        config = json.loads(runner.CONFIG.read_text())
        capabilities = {"architecture": "x86_64", "features": {"sse2": True}}
        standard = runner.selected_plan(options, config, capabilities)["jobs"]
        options.disable_slp = True
        workaround = runner.selected_plan(options, config, capabilities)["jobs"]
        self.assertEqual(len(standard), 1)
        self.assertEqual(len(workaround), 1)
        self.assertNotEqual(standard[0]["id"], workaround[0]["id"])
        self.assertEqual(standard[0]["features"], workaround[0]["features"])
        self.assertNotIn("extra_rustflags", standard[0])
        self.assertEqual(workaround[0]["extra_rustflags"], ["-C", "no-vectorize-slp"])

    def test_affected_tiny_builds_apply_fix_without_changing_other_backends(self):
        import json
        options = self.options()
        config = json.loads(runner.CONFIG.read_text())
        capabilities = {"architecture": "x86_64", "features": {
            feature: True for target in config["targets"] for feature in target["requires"]}}
        jobs = runner.selected_plan(options, config, capabilities)["jobs"]
        fixed = [job for job in jobs if "extra_rustflags" in job]
        self.assertEqual(len(fixed), 6)
        self.assertEqual({job["target"]["id"] for job in fixed}, {"v3", "v4", "native"})
        self.assertTrue(all(job["keccak"] == "tiny" for job in fixed))
        self.assertTrue(all(job["id"].endswith("-no-slp") for job in fixed))
        options.unmodified_tiny = True
        original = runner.selected_plan(options, config, capabilities)["jobs"]
        self.assertTrue(all("extra_rustflags" not in job for job in original))

    def test_rust_preset_covers_all_backends_and_both_recovery_providers(self):
        import json
        options = self.options()
        options.profile = "rust"
        config = json.loads(runner.CONFIG.read_text())
        capabilities = {"architecture": "x86_64", "features": {
            feature: True for target in config["targets"] for feature in target["requires"]}}
        plan = runner.selected_plan(options, config, capabilities)
        self.assertEqual(len(plan["jobs"]), 30)
        self.assertEqual(plan["profile"]["samples"], 40)
        self.assertEqual(plan["cooldown_seconds"], 2)
        primary = [job for job in plan["jobs"] if job["ecrecover"] == "libsecp256k1"]
        self.assertEqual(len(primary), 15)
        self.assertTrue(all(job["groups"] == ["macro", "reject", "hash"] for job in primary))
        self.assertTrue(all(job["groups"] == ["ecrecover"] for job in plan["jobs"] if job["ecrecover"] == "k256"))

    def test_unknown_backend_is_rejected_before_build(self):
        import json
        options = self.options()
        options.hashing = "typo"
        with self.assertRaises(ValueError):
            runner.selected_plan(options, json.loads(runner.CONFIG.read_text()),
                                 {"architecture": "x86_64", "features": {"sse2": True}})



class MachineTests(unittest.TestCase):
    def test_frequency_can_change_without_changing_policy(self):
        initial = {"processors": [{"Name": "CPU", "CurrentClockSpeed": 2000}], "power_scheme": "scheme"}
        current = {"processors": [{"Name": "CPU", "CurrentClockSpeed": 4000}], "power_scheme": "scheme"}
        host.require_same_machine(initial, current)
        current["power_scheme"] = "different"
        with self.assertRaises(ValueError):
            host.require_same_machine(initial, current)

    def test_retry_archive_preserves_partial_data(self):
        import tempfile
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            original = root / "task.partial.json"
            original.write_text("preserve this")
            archived = host.archive_attempt(root, "task")
            self.assertFalse(original.exists())
            self.assertEqual((root / archived / original.name).read_text(), "preserve this")

    def test_clock_samples_outside_timed_batches_are_excluded(self):
        import json
        import tempfile
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "clock.jsonl"
            path.write_text(json.dumps({"utc": "2026-01-01T00:00:00Z", "reported_frequency_mhz": 1000}) + "\n" +
                            json.dumps({"utc": "2026-01-01T00:00:01Z", "reported_frequency_mhz": 4000}) + "\n")
            report = {"measurements": [{"samples": [{"started_unix_ns": 1767225601000000000, "elapsed_ns": 200000000}]}]}
            result = host.telemetry_summary([path], [report])
            self.assertEqual(result["observations"], 1)
            self.assertEqual(result["median_reported_mhz"], 4000)



class ReportTests(unittest.TestCase):
    def test_readme_uses_backend_names_and_omits_local_run_metadata(self):
        from suite import publication
        state = {"machine": {"processors": [{"Name": "Example CPU"}],
                             "power_scheme": "PRIVATE_POWER_POLICY", "bios_version": "PRIVATE_BIOS"},
                 "notes": "PRIVATE_LOCAL_NOTES", "plan": {"cpu": 2, "profile": {"samples": 40, "passes": 1}},
                 "builds": {"rustc": "rustc 1.97.1\nLLVM version: 22.1.6", "jobs": {
                     "native-tiny-libsecp256k1-no-slp": {"configuration": {
                         "target": {"id": "native"}, "keccak": "tiny", "ecrecover": "libsecp256k1"}}}}}
        rows = [{"configuration": "native-tiny-libsecp256k1-no-slp", "name": name, "median_ns": value}
                for name, value in [("macro/native/verify_wire/mixed", 200000),
                                    ("macro/reference/verify_wire/mixed", 300000),
                                    ("macro/evm2/ecrecover", 100000)]]
        draft = publication.render(state, rows)
        self.assertIn("| native | tiny-keccak | 200.00 | 300.00 | +50.0% |", draft)
        self.assertIn("#### evm2 libsecp256k1", draft)
        for value in ["PRIVATE_POWER_POLICY", "PRIVATE_BIOS", "PRIVATE_LOCAL_NOTES", "no-slp", "Alternative Rust"]:
            self.assertNotIn(value, draft)
        with self.assertRaises(ValueError):
            publication.render(state, rows + rows)

    def test_completed_synthetic_session_generates_auditable_tables(self):
        import json
        import tempfile
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "corpus.json").write_text("synthetic public fixture")
            def measurement(name, elapsed):
                return {"name": name, "samples": [
                    {"index": i, "iterations": 1, "work_items": 1,
                     "elapsed_ns": elapsed, "ns_per_op": float(elapsed)}
                    for i in range(5)]}
            data = {"schema_version": 1, "status": "complete", "measurements": [
                measurement("macro/native/verify_wire/mixed", 200),
                measurement("macro/reference/verify_wire/mixed", 300),
                measurement("macro/evm2/ecrecover", 100),
            ]}
            host.write_json(root / "raw.json", data)
            configuration = "baseline-portable-libsecp256k1"
            state = {
                "finished_utc": "synthetic test",
                "corpus_sha256": host.digest(root / "corpus.json"),
                "plan": {"cpu": 2, "profile": {"samples": 5, "passes": 1, "sample_ms": 200}},
                "source": {"revision": "synthetic"},
                "machine": {"processors": [{"Name": "Synthetic CPU"}]},
                "builds": {"rustc": "synthetic compiler", "jobs": {configuration: {
                    "rustflags": ["-C", "target-cpu=x86-64"],
                    "build": {"build": {"paired_fors": True, "reference_batch_lanes": 1}},
                }}},
                "completed": {"task": {"configuration": configuration, "file": "raw.json",
                                       "sha256": host.digest(root / "raw.json")}},
            }
            host.write_json(root / "session.json", state)
            runner.report_session(argparse.Namespace(session=str(root), bootstrap=100,
                                                     include_reference=False))
            draft = (root / "README-benchmarks.md").read_text(encoding="utf-8")
            self.assertIn("Synthetic CPU", draft)
            self.assertNotIn("macro/reference/verify_wire/mixed", draft)
            calibration = json.loads((root / "calibration.json").read_text())
            self.assertEqual(calibration[0]["cpu_ratio_at_3000"], 6000)
            self.assertFalse(calibration[0]["consensus_price"])
            self.assertTrue((root / "summary.csv").is_file())


if __name__ == "__main__":
    unittest.main()
