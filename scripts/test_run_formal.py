"""Regression checks for the formal comparison gate's fail-closed behavior."""

import unittest
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch
from run_formal import COMPONENT_KINDS, check_output, expected_lines, run_checked


class FormalOutputTests(unittest.TestCase):
    def setUp(self):
        self.manifest = {"schema_version": 1, "cases": [
            {"kind": kind, "name": "case"} for kind in ("key_gen", "sign", "verify")
        ]}
        self.lines = sorted(expected_lines(self.manifest))

    def test_complete_comparison(self):
        self.assertEqual(check_output(self.manifest, "\n".join(self.lines + ["0 mismatches"])), 3)

    def test_no_cases_cannot_pass(self):
        with self.assertRaises(ValueError):
            check_output(self.manifest, "0 mismatches\n")
        with self.assertRaises(ValueError):
            expected_lines({"schema_version": 1, "cases": []})

    def test_missing_duplicate_and_mismatched_cases_fail(self):
        for lines in (self.lines[:-1], self.lines + self.lines[:1],
                      [self.lines[0].replace(": ok", ": MISMATCH")] + self.lines[1:]):
            with self.subTest(lines=lines), self.assertRaises(ValueError):
                check_output(self.manifest, "\n".join(lines + ["0 mismatches"]))

    def test_nonzero_or_missing_summary_fails(self):
        for summary in ("1 mismatches", "", "256 mismatches"):
            with self.subTest(summary=summary), self.assertRaises(ValueError):
                check_output(self.manifest, "\n".join(self.lines + [summary]))

    def test_invalid_and_duplicate_manifest_cases_fail(self):
        for case in ({"kind": "verify", "name": "../case"}, self.manifest["cases"][0]):
            with self.subTest(case=case), self.assertRaises(ValueError):
                expected_lines({"schema_version": 1, "cases": self.manifest["cases"] + [case]})

    def test_unexpected_or_incomplete_output_fails(self):
        for extra in ("unexpected result", "sphincs verify unlisted: ok", "0 mismatches"):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                check_output(self.manifest, "\n".join(self.lines + [extra, "0 mismatches"]))

    def test_component_inventory_cannot_be_skipped(self):
        manifest = {"schema_version": 1, "cases": [{"kind": k, "name": "case"} for k in COMPONENT_KINDS]}
        self.assertEqual(len(expected_lines(manifest, COMPONENT_KINDS)), len(COMPONENT_KINDS))
        manifest["cases"].pop()
        with self.assertRaises(ValueError):
            expected_lines(manifest, COMPONENT_KINDS)

    def test_process_failure_is_rejected_even_with_perfect_stdout(self):
        output = "\n".join(self.lines + ["0 mismatches"])
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "comparison.log"
            corpus = Path(directory) / "corpus"
            for case in self.manifest["cases"]:
                path = corpus / "lean_sphincs/tests/lean_sphincs/ethlib" / case["kind"] / case["name"] / "data.yaml"
                path.parent.mkdir(parents=True)
                path.write_text("output: null\n")
            for code, stderr in [(1, ""), (256, ""), (0, "unexpected diagnostic")]:
                result = subprocess.CompletedProcess([], code, output, stderr)
                with self.subTest(code=code, stderr=stderr), patch("run_formal.subprocess.run", return_value=result):
                    with self.assertRaises(ValueError):
                        run_checked(Path("model"), corpus, self.manifest,
                                    {"key_gen", "sign", "verify"}, log)
                    self.assertIn("0 mismatches", log.read_text())


if __name__ == "__main__":
    unittest.main()
