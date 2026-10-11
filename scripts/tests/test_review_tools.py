"""Regressions for the review boundary and the guide's generated appendix."""
import copy
import importlib.util
import io
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


status = load("status", ROOT / "scripts/status.py")
GUIDE_TOOLS = ROOT / "textbook/tutorial/tools"
with patch.object(sys, "path", [str(GUIDE_TOOLS), *sys.path]):
    listings = load("extract_listings", GUIDE_TOOLS / "extract_listings.py")


class ReviewTests(unittest.TestCase):
    def setUp(self):
        self.statement = {"decl": "Artform.Statement.test", "text": "P", "surface": ["D"],
                          "terms": ["exact P", "exact D"]}
        self.entry = {"key": "prop:test", "status": "proved", "reviewed": "2026-10-11",
                      "book_sha256": "book hash", "fidelity": "Same claim."}
        self.definitions = [{"key": "def:test", "status": "defined", "fidelity": "Same definition."}]
        self.inventory = {
            "prop:test": {"kind": "proposition", "statement": "Book proposition.",
                          "statement_sha256": "book hash"},
            "def:test": {"kind": "definition", "statement": "Book definition."},
        }
        self.report = ({"prop:test": self.statement},
                       {"prop:test": [{"decl": "Artform.test", "proves": self.statement["decl"],
                                       "axioms": ["propext"]}]},
                       {"def:test": [{"decl": "Artform.D"}]}, [])
        self.entry.update(review_text_sha256=status.text_hash(self.statement),
                          review_term_sha256=status.term_hash(self.statement),
                          review_context_sha256=status.context_hash(
                              self.entry, self.definitions, self.inventory))

    def result(self):
        results, _, problems, _ = status.evaluate(
            [self.entry], self.definitions, self.inventory, self.report)
        self.assertEqual(problems, [])
        return results[0]

    def test_unchanged_review_stays_proved(self):
        self.assertEqual(self.result()["status"], "proved")

    def test_book_definition_change_revokes_review_even_with_unchanged_stored_hash(self):
        self.inventory["def:test"]["statement"] = "Changed book definition."
        self.assertEqual(self.result()["status"], "stated")

    def test_fidelity_change_revokes_review(self):
        self.entry["fidelity"] = "A new restriction."
        self.assertEqual(self.result()["status"], "stated")

    def test_definition_fidelity_change_revokes_review(self):
        self.definitions[0]["fidelity"] = "A different interpretation."
        self.assertEqual(self.result()["status"], "stated")

    def test_missing_context_hash_revokes_legacy_review(self):
        del self.entry["review_context_sha256"]
        self.assertEqual(self.result()["status"], "stated")

    def test_return_verdict_blocks_an_old_approval(self):
        self.entry["review_return"] = "Missing a book case."
        self.assertEqual(self.result()["status"], "stated")
        self.assertIn("returned: Missing a book case.", self.result()["notes"])

    def test_renumbering_and_relocation_preserve_review(self):
        self.inventory["def:test"].update(number="2.1", file="moved.tex", line=25)
        self.assertEqual(self.result()["status"], "proved")

    def test_lean_dependency_change_still_revokes_review(self):
        self.statement["terms"].append("changed dependency")
        self.assertEqual(self.result()["status"], "stated")

    def test_bad_proof_cannot_write_an_approval(self):
        self.report[1]["prop:test"][0]["axioms"].append("sorryAx")
        with tempfile.TemporaryDirectory() as tmp:
            manifest, log = Path(tmp) / "manifest.toml", Path(tmp) / "review-log.md"
            source = '[[statement]]\nkey = "prop:test"\nstatus = "stated"\n'
            source += '[[definition]]\nkey = "def:test"\nstatus = "defined"\n'
            manifest.write_text(source)
            with patch.object(status, "MANIFEST", manifest), patch.object(status, "REVIEW_LOG", log):
                with self.assertRaises(SystemExit):
                    status.approve(["prop:test"], "2026-10-11", self.report, self.inventory)
            self.assertEqual(manifest.read_text(), source)
            self.assertFalse(log.exists())

    def test_bad_report_cannot_write_guide_status(self):
        bad_report = copy.deepcopy(self.report)
        bad_report[1]["prop:test"][0]["axioms"].append("sorryAx")
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "status.tex"
            with patch.object(sys, "argv", ["status.py", "--tex", str(output)]), \
                    patch.object(status, "load_report", return_value=bad_report), \
                    patch.object(status, "load_inventory", return_value=(None, self.inventory)), \
                    patch.object(status, "load_manifest", return_value=("", [self.entry], self.definitions)), \
                    patch.object(status, "set_fields", side_effect=lambda text, *_: text), \
                    redirect_stdout(io.StringIO()):
                self.assertEqual(status.main(), 1)
            self.assertFalse(output.exists())


class GuideFreshnessTests(unittest.TestCase):
    def test_status_sources_are_part_of_pdf_freshness(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            textbook = root / "textbook"
            tutorial = textbook / "tutorial"
            tex = tutorial / "tex"
            snippets = tex / "snippets"
            snippets.mkdir(parents=True)
            (root / "scripts").mkdir()
            (textbook / "edition.toml").write_text('inventory = "inventory.json"\n')
            sources = [textbook / "manifest.toml", textbook / "inventory.json",
                       root / "scripts/status.py"]
            for source in sources:
                source.write_text("original")
            with patch.object(listings, "TUTORIAL", tutorial), patch.object(listings, "TEX", tex):
                original = listings.inputs_hash(snippets)
                for source in [*sources, textbook / "edition.toml"]:
                    with self.subTest(source=source.name):
                        before = source.read_text()
                        source.write_text(before + "\n# changed\n")
                        self.assertNotEqual(listings.inputs_hash(snippets), original)
                        source.write_text(before)
                self.assertEqual(listings.inputs_hash(snippets), original)


if __name__ == "__main__":
    unittest.main()
