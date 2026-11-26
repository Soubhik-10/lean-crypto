"""Regression checks against stale, incomplete or falsely successful translation evidence."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("translate_sphincs", ROOT / "scripts/translate_sphincs.py")
translation = importlib.util.module_from_spec(spec)
spec.loader.exec_module(translation)


class TranslationGuards(unittest.TestCase):
    def setUp(self):
        cache = ROOT / "formal/.cache"
        cache.mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="translation-test-", dir=cache)
        self.root = Path(self.temp.name).resolve()
        self.assertTrue(self.root.is_relative_to(cache.resolve()))
        self.addCleanup(self.temp.cleanup)
        (self.root / "formal").mkdir()
        (self.root / "formal/extractor.json").write_text(json.dumps({"charon": {"version": "pinned"}}))
        self.run = self.root / "formal/.cache/extraction-runs/test"
        self.run.mkdir(parents=True)
        self.manifest = {"sources": {"source": "current"}, "charon_binary": {"sysroot": "default"}, "variants": []}
        for name in translation.extraction.VARIANTS:
            folder = self.run / name
            folder.mkdir()
            data = json.dumps({"has_errors": False, "charon_version": "pinned",
                               "translated": {"crate_name": "lean_sphincs"}}).encode()
            (folder / "lean_sphincs.llbc").write_bytes(data)
            self.manifest["variants"].append({"variant": name, "has_errors": False,
                "sha256": hashlib.sha256(data).hexdigest()})
        self.save()
        for patcher in (patch.object(translation, "ROOT", self.root),
                        patch.object(translation.extraction, "source_snapshot", return_value={"source": "current"})):
            patcher.start()
            self.addCleanup(patcher.stop)

    def save(self):
        (self.run / "manifest.json").write_text(json.dumps(self.manifest))

    def alter_artifact(self, **changes):
        path = self.run / "sse2/lean_sphincs.llbc"
        data = json.loads(path.read_bytes())
        data.update(changes)
        content = json.dumps(data).encode()
        path.write_bytes(content)
        self.manifest["variants"][0]["sha256"] = hashlib.sha256(content).hexdigest()
        self.save()

    def test_complete_current_extraction_accepted(self):
        self.assertEqual(translation.load_extraction(self.run), self.manifest)

    def test_stale_source_rejected(self):
        self.manifest["sources"] = {"source": "old"}
        self.save()
        with self.assertRaisesRegex(RuntimeError, "source differs"):
            translation.load_extraction(self.run)

    def test_missing_configuration_rejected(self):
        self.manifest["variants"].pop()
        self.save()
        with self.assertRaisesRegex(RuntimeError, "exactly once"):
            translation.load_extraction(self.run)

    def test_duplicate_configuration_rejected(self):
        self.manifest["variants"].append(self.manifest["variants"][0])
        self.save()
        with self.assertRaisesRegex(RuntimeError, "exactly once"):
            translation.load_extraction(self.run)

    def test_different_stdlib_sysroot_rejected(self):
        self.manifest["charon_binary"]["sysroot"] = "full-mir"
        self.save()
        with self.assertRaisesRegex(RuntimeError, "pinned default Rust sysroot"):
            translation.load_extraction(self.run)

    def test_changed_artifact_rejected(self):
        (self.run / "sse2/lean_sphincs.llbc").write_bytes(b"changed")
        with self.assertRaisesRegex(RuntimeError, "hash differs"):
            translation.load_extraction(self.run)

    def test_errorful_extraction_rejected_even_with_matching_hash(self):
        self.alter_artifact(has_errors=True)
        with self.assertRaisesRegex(RuntimeError, "contains errors"):
            translation.load_extraction(self.run)

    def test_wrong_crate_rejected_even_with_matching_hash(self):
        self.alter_artifact(translated={"crate_name": "other"})
        with self.assertRaisesRegex(RuntimeError, "unexpected extracted crate"):
            translation.load_extraction(self.run)

    def test_incompatible_charon_rejected(self):
        self.alter_artifact(charon_version="wrong")
        with self.assertRaisesRegex(RuntimeError, "Charon version differs"):
            translation.load_extraction(self.run)

    def test_exit_zero_without_generated_lean_is_failure(self):
        result = subprocess.CompletedProcess([], 0, stdout="")
        self.assertFalse(translation.summarize(result, self.run)[0])

    def test_colored_diagnostic_prevents_false_success(self):
        (self.run / "Generated.lean").write_text("module")
        result = subprocess.CompletedProcess([], 0, stdout="[\x1b[91mError\x1b[39m] failed")
        success, diagnostics, _ = translation.summarize(result, self.run)
        self.assertFalse(success)
        self.assertIn("[Error] failed", diagnostics)

    def complete_inventory(self):
        (self.run / "translation.json").write_text(json.dumps({"crate": "lean_sphincs", "functions": [
            {"rust_name": name, "is_local": True, "is_opaque": False}
            for name in ("lean_sphincs::verify", "lean_sphincs::signing::key_gen", "lean_sphincs::signing::sign")]}))
        (self.run / "Funs.lean").write_text("module\n")

    def test_empty_translation_cannot_count_as_whole_crate(self):
        (self.run / "translation.json").write_text(json.dumps({"crate": "lean_sphincs", "functions": []}))
        (self.run / "Funs.lean").write_text("module\n")
        result = subprocess.CompletedProcess([], 0, stdout="")
        self.assertFalse(translation.summarize(result, self.run)[0])

    def test_opaque_local_body_rejected(self):
        self.complete_inventory()
        path = self.run / "translation.json"
        data = json.loads(path.read_text())
        data["functions"][0]["is_opaque"] = True
        path.write_text(json.dumps(data))
        self.assertIn("opaque local function: lean_sphincs::verify", translation.inspect_bindings(self.run)[0])

    def test_generated_proof_hole_rejected(self):
        self.complete_inventory()
        (self.run / "Funs.lean").write_text("def unfinished : Nat := by sorry\n")
        result = subprocess.CompletedProcess([], 0, stdout="")
        self.assertFalse(translation.summarize(result, self.run)[0])

    def test_external_templates_remain_explicit_obligations(self):
        self.complete_inventory()
        (self.run / "FunsExternal_Template.lean").write_text("axiom externalHash : Nat\n")
        problems, models = translation.inspect_bindings(self.run)
        self.assertEqual(problems, [])
        self.assertEqual(models, ["externalHash"])

    def test_complete_translation_is_distinct_from_correctness(self):
        self.complete_inventory()
        result = subprocess.CompletedProcess([], 0, stdout="")
        self.assertTrue(translation.summarize(result, self.run)[0])

    def complete_translation_report(self):
        destination = self.root / "translation"
        destination.mkdir()
        results = []
        for name in translation.extraction.VARIANTS:
            folder = destination / name
            folder.mkdir()
            (folder / "Types.lean").write_text("module\n")
            (folder / "Funs.lean").write_text("module\ndef function := 0\n")
            inventory = {"crate": "lean_sphincs", "functions": [
                {"rust_name": n, "is_local": True, "is_opaque": False}
                for n in ("lean_sphincs::verify", "lean_sphincs::signing::key_gen", "lean_sphincs::signing::sign")]}
            (folder / "translation.json").write_text(json.dumps(inventory))
            results.append({"variant": name, "translated": True,
                            "generated_sha256": translation.binding_hashes(folder)})
        report = {"sources": self.manifest["sources"], "results": results,
                  "translation_passed": True, "requested_toolchain": {"charon": {"version": "pinned"}},
                  "extraction_run": self.run.relative_to(self.root).as_posix(),
                  "extraction_manifest_sha256": hashlib.sha256((self.run / "manifest.json").read_bytes()).hexdigest()}
        (destination / "report.json").write_text(json.dumps(report))
        return destination

    def test_source_to_body_provenance_accepted(self):
        self.assertTrue(translation.load_translation(self.complete_translation_report())["translation_passed"])

    def test_edited_generated_body_rejected(self):
        destination = self.complete_translation_report()
        (destination / "sse2/Funs.lean").write_text("module\ndef function := 1\n")
        with self.assertRaisesRegex(RuntimeError, "body or declaration inventory hash differs"):
            translation.load_translation(destination)

    def test_edited_declaration_inventory_rejected(self):
        destination = self.complete_translation_report()
        (destination / "avx2/translation.json").write_text("{}")
        with self.assertRaisesRegex(RuntimeError, "body or declaration inventory hash differs"):
            translation.load_translation(destination)

    def test_toolchain_changed_after_translation_rejected(self):
        destination = self.complete_translation_report()
        (self.root / "formal/extractor.json").write_text(json.dumps({"charon": {"version": "changed"}}))
        with self.assertRaisesRegex(RuntimeError, "toolchain pin changed"):
            translation.load_translation(destination)

    def test_extraction_manifest_changed_after_translation_rejected(self):
        destination = self.complete_translation_report()
        self.manifest["sources"] = {"source": "changed"}
        self.save()
        with self.assertRaisesRegex(RuntimeError, "manifest hash differs"):
            translation.load_translation(destination)

    def test_nonzero_exit_rejected_despite_generated_files(self):
        (self.run / "Generated.lean").write_text("module")
        result = subprocess.CompletedProcess([], 2, stdout="")
        self.assertFalse(translation.summarize(result, self.run)[0])


if __name__ == "__main__":
    unittest.main()
