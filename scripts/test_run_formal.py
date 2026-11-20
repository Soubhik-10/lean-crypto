"""Regression checks for the formal comparison gate's fail-closed behavior."""

import unittest
from run_formal import check_output, expected_lines


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


if __name__ == "__main__":
    unittest.main()
