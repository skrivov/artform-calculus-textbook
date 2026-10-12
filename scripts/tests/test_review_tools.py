"""Regressions for the review boundary and the guide's generated appendix."""
import copy
import importlib.util
import io
import sys
import tempfile
import tomllib
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
GUIDE_TOOLS = ROOT / "tutorial/tools"
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
        self.entry.update(review_text_sha256=status.text_hash(self.statement))

    def result(self):
        results, _, problems, _ = status.evaluate(
            [self.entry], self.definitions, self.inventory, self.report)
        self.assertEqual(problems, [])
        return results[0]

    def drift(self):
        return status.drift([self.entry], self.inventory, self.report)

    def test_unchanged_review_stays_proved(self):
        self.assertEqual(self.result()["status"], "proved")
        self.assertEqual(self.drift(), [])

    def test_unreviewed_statement_awaits_review(self):
        del self.entry["reviewed"]
        self.assertEqual(self.result()["status"], "stated")
        self.assertEqual(self.result()["notes"], ["awaits review"])

    def test_return_verdict_blocks_an_old_approval(self):
        self.entry["review_return"] = "Missing a book case."
        self.assertEqual(self.result()["status"], "stated")
        self.assertIn("returned: Missing a book case.", self.result()["notes"])
        self.assertEqual(self.drift(), [])

    def test_missing_proof_keeps_an_approved_statement_stated(self):
        self.report[1]["prop:test"].clear()
        self.assertEqual(self.result()["status"], "stated")
        self.assertEqual(self.result()["notes"], ["no proof yet"])

    def test_rebuilds_moves_and_new_definitions_do_not_touch_a_review(self):
        # A move renames hygienic binders in the exact terms; new definitions,
        # fidelity notes and a renumbered book change the context.
        self.statement["terms"].append("inst._@.ArtformTextbook.Moved._hyg.12")
        self.definitions.append({"key": "def:new", "status": "defined", "fidelity": "New."})
        self.inventory["def:new"] = {"kind": "definition", "statement": "Another definition."}
        self.definitions[0]["fidelity"] = "A different interpretation."
        self.entry["fidelity"] = "A clarified note."
        self.inventory["def:test"].update(statement="Changed book definition.", number="2.1")
        self.assertEqual(self.result()["status"], "proved")
        self.assertEqual(self.drift(), [])

    def test_changed_lean_text_keeps_the_approval_and_is_listed(self):
        self.statement["surface"] = ["D, changed"]
        self.assertEqual(self.result()["status"], "proved")
        self.assertEqual(self.result()["notes"], [])
        self.assertEqual(self.drift(), [("prop:test", ["Lean text"])])

    def test_changed_book_text_keeps_the_approval_and_is_listed(self):
        self.inventory["prop:test"]["statement_sha256"] = "new book hash"
        self.assertEqual(self.result()["status"], "proved")
        self.assertEqual(self.drift(), [("prop:test", ["book text"])])

    def test_approval_records_the_reviewed_text_and_clears_a_return(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest, log = Path(tmp) / "manifest.toml", Path(tmp) / "review-log.md"
            manifest.write_text('[[statement]]\nkey = "prop:test"\nstatus = "stated"\n'
                                'review_return = "Missing a book case."\n'
                                '[[definition]]\nkey = "def:test"\nstatus = "defined"\n')
            with patch.object(status, "MANIFEST", manifest), patch.object(status, "REVIEW_LOG", log), \
                    redirect_stdout(io.StringIO()):
                status.approve(["prop:test"], "2026-10-12", self.report, self.inventory)
            entry = tomllib.loads(manifest.read_text())["statement"][0]
            self.assertEqual(entry["reviewed"], "2026-10-12")
            self.assertEqual(entry["review_text_sha256"], status.text_hash(self.statement))
            self.assertEqual(entry["book_sha256"], "book hash")
            self.assertEqual(entry["review_return"], "")
            self.assertIn("`prop:test` approved", log.read_text())

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
            tutorial = root / "tutorial"
            tex = tutorial / "tex"
            snippets = tex / "snippets"
            snippets.mkdir(parents=True)
            textbook.mkdir()
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
