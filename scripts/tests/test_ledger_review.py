"""Check that scores verdicts cannot be confused with proof availability."""
import copy
import importlib.util
import io
import tempfile
import tomllib
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("ledger_status", ROOT / "scripts/ledger_status.py")
ledger = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ledger)


class LedgerReviewTests(unittest.TestCase):
    def setUp(self):
        self.entry = {"key": "T:test", "label": "T", "title": "Test",
                      "lean_statement": "Artform.Scores.Statement.test",
                      "lean_proof": "Artform.Scores.test", "reviewed": "",
                      "review_text_sha256": ""}
        self.row = {"kind": "statement", "label": "T", "decl": self.entry["lean_statement"],
                    "text": "P", "surface": ["D"]}
        self.proof = {"kind": "proof", "label": "T", "decl": self.entry["lean_proof"],
                      "proves": self.row["decl"], "axioms": ["propext"]}
        self.report = [self.row, self.proof]

    def test_proof_without_approval_is_not_proved(self):
        results, problems = ledger.evaluate([self.entry], self.report)
        self.assertEqual(problems, [])
        self.assertEqual(results[0][1], "stated")
        self.assertIn("awaiting review", ledger.render(results))

    def test_return_overrides_approval_without_erasing_it(self):
        self.entry.update(reviewed="2026-10-30", review_return="Missing case.",
                          review_text_sha256="old hash")
        results, problems = ledger.evaluate([self.entry], self.report)
        self.assertEqual(problems, [])
        self.assertEqual(results[0][1], "stated")
        self.assertFalse(results[0][2])
        self.assertIn("returned: Missing case.", ledger.render(results))
        self.assertEqual(self.entry["reviewed"], "2026-10-30")

    def test_text_drift_preserves_an_approval(self):
        self.entry.update(reviewed="2026-10-30", review_text_sha256="old hash")
        results, problems = ledger.evaluate([self.entry], self.report)
        self.assertEqual(problems, [])
        self.assertEqual(results[0][1:], ("proved", True))

    def approve_in_temp(self, entries, report, source):
        with tempfile.TemporaryDirectory() as tmp:
            manifest, log = Path(tmp) / "manifest.toml", Path(tmp) / "review-log.md"
            manifest.write_text(source)
            with patch.object(ledger, "MANIFEST", manifest), \
                    patch.object(ledger, "REVIEW_LOG", log), redirect_stdout(io.StringIO()):
                try:
                    ledger.approve([self.entry["key"]], "2026-10-30", entries, report)
                except SystemExit:
                    self.assertEqual(manifest.read_text(), source)
                    self.assertFalse(log.exists())
                    raise
            return tomllib.loads(manifest.read_text()), log.read_text()

    def source(self):
        return ('[[statement]]\nkey = "T:test"\nreviewed = ""\n'
                'review_text_sha256 = ""\nreview_return = "Missing case."\n')

    def test_approval_clears_a_return_and_records_hash(self):
        data, log = self.approve_in_temp([self.entry], self.report, self.source())
        entry = data["statement"][0]
        self.assertEqual(entry["reviewed"], "2026-10-30")
        self.assertEqual(entry["review_text_sha256"], ledger.text_hash(self.row))
        self.assertFalse(entry.get("review_return"))
        self.assertIn("`T:test` approved", log)

    def test_duplicate_keys_cannot_record_an_approval(self):
        duplicate = copy.deepcopy(self.entry)
        results, problems = ledger.evaluate([self.entry, duplicate], self.report)
        self.assertIn("duplicate manifest key", "; ".join(problems))
        with self.assertRaises(SystemExit):
            self.approve_in_temp([self.entry, duplicate], self.report, self.source() * 2)

    def test_untrusted_axiom_cannot_record_an_approval(self):
        self.proof["axioms"].append("sorryAx")
        with self.assertRaises(SystemExit):
            self.approve_in_temp([self.entry], self.report, self.source())


if __name__ == "__main__":
    unittest.main()
