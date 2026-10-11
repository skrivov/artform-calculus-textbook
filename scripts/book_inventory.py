#!/usr/bin/env python3
"""The textbook's numbered statements and definitions, as the book prints them.

Run locally, where the book's sources are, whenever the repository follows a
new edition:

  python3 scripts/book_inventory.py BOOKDIR NUMBER [--out PATH]

BOOKDIR holds artform-calculus-and-applications.tex and its .aux; NUMBER is
the edition's number. The default output is
textbook/inventory/edition-<NUMBER>.json.

The script walks the book's \\input graph in reading order. For every theorem,
proposition, lemma, corollary and definition it records:
- the key: the label, or nolabel:<file>:<title> when there is none;
- kind, title, label, number, page, source file and line;
- chapter, section, and whether the section is on the optional (lozenge)
  track;
- the statement's LaTeX and the SHA-256 of its whitespace-normalised text;
- whether a proof follows, its title and length, and the labels that the
  statement and the proof cite.

Numbers come from the .aux, and from counting the theorem counter when an item
has no label. The count is checked against the .aux for every labelled item.
Proof texts are not stored.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAIN = "artform-calculus-and-applications"
RECORDED = ("theorem", "proposition", "lemma", "corollary", "definition")
COUNTED = RECORDED + ("example", "principle")      # share the theorem counter
INPUT = re.compile(r"\\(?:input|include)\{([^}]+)\}")
BEGIN = re.compile(r"\\begin\{(" + "|".join(COUNTED) + r")\}(\[)?")
HEADING = re.compile(r"\\(chapter|section|subsection)(\*?)(?:\[[^\]]*\])?\s*\{")
APPENDIX = re.compile(r"\\appendix\b")
REF = re.compile(r"\\(?:ref|cref|Cref|eqref|autoref|pageref)\{([^}]+)\}")


def strip_comments(line):
    return re.sub(r"(?<!\\)%.*", "", line)


def balanced(text, i, open_ch, close_ch):
    """text[i] == open_ch; the index just after its matching close."""
    depth = 0
    for j in range(i, len(text)):
        c = text[j]
        if c == open_ch and (j == 0 or text[j - 1] != "\\"):
            depth += 1
        elif c == close_ch and text[j - 1] != "\\":
            depth -= 1
            if depth == 0:
                return j + 1
    return len(text)


def slug(s):
    return re.sub(r"[^a-z0-9]+", "-", s.lower()).strip("-")


def labels_of(refs):
    return sorted({r.strip() for group in refs for r in group.split(",")})


class Walker:
    def __init__(self, book):
        self.book = book
        self.items = []
        self.seen = set()
        self.chapter_no = 0
        self.appendix = False
        self.counter = 0
        self.ctx = {"chapter": "", "section": "", "optional": False}

    def resolve(self, name, here):
        for base in (here.parent, self.book):
            q = base / name
            if not q.suffix:
                q = q.with_suffix(".tex")
            if q.exists():
                return q
        return None

    def chapter_label(self):
        if self.appendix:
            return chr(ord("A") + self.chapter_no - 1)
        return str(self.chapter_no)

    def walk(self, path):
        if path in self.seen:
            return
        self.seen.add(path)
        lines = [strip_comments(x) for x in path.read_text(errors="ignore").split("\n")]
        text = "\n".join(lines)
        starts, o = [], 0
        for x in lines:
            starts.append(o)
            o += len(x) + 1

        def lineno(off):
            lo, hi = 0, len(starts) - 1
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if starts[mid] <= off:
                    lo = mid
                else:
                    hi = mid - 1
            return lo + 1

        events = [(m.start(), "input", m) for m in INPUT.finditer(text)]
        events += [(m.start(), "env", m) for m in BEGIN.finditer(text)]
        events += [(m.start(), "heading", m) for m in HEADING.finditer(text)]
        events += [(m.start(), "appendix", m) for m in APPENDIX.finditer(text)]
        events.sort(key=lambda e: e[0])
        skip_until = -1
        for off, kind, m in events:
            if off < skip_until:
                continue
            if kind == "input":
                q = self.resolve(m.group(1), path)
                if q:
                    self.walk(q)
            elif kind == "appendix":
                self.appendix, self.chapter_no = True, 0
            elif kind == "heading":
                j = balanced(text, m.end() - 1, "{", "}")
                title = " ".join(text[m.end():j - 1].split())
                level, starred = m.group(1), m.group(2) == "*"
                if level == "chapter":
                    if not starred:
                        self.chapter_no += 1
                        self.counter = 0
                    self.ctx = {"chapter": title, "section": "", "optional": False}
                elif level == "section":
                    self.ctx["section"] = title
                    self.ctx["optional"] = "optionalmark" in title
            else:
                env = m.group(1)
                self.counter += 1
                number = f"{self.chapter_label()}.{self.counter}"
                end = text.find("\\end{%s}" % env, m.end())
                if env not in RECORDED:
                    skip_until = end
                    continue
                title, k = "", m.end()
                if m.group(2):
                    j = balanced(text, k - 1, "[", "]")
                    title = " ".join(text[k:j - 1].split())
                    k = j
                body = text[k:end]
                labels = re.findall(r"\\label\{([^}]+)\}", body)
                after = end + len("\\end{%s}" % env)
                pm = re.match(r"\s*\\begin\{proof\}(\[[^\]]*\])?", text[after:])
                proof, proof_title = "", ""
                if pm:
                    pend = text.find("\\end{proof}", after + pm.end())
                    proof = text[after + pm.end():pend]
                    proof_title = (pm.group(1) or "").strip("[]")
                statement = re.sub(r"\\label\{[^}]+\}", "", body).strip()
                label = labels[0] if labels else ""
                self.items.append({
                    "key": label or "nolabel:%s:%s" % (path.stem, slug(title)),
                    "kind": env, "title": title, "label": label,
                    "number": number, "page": "",
                    "file": str(path.relative_to(self.book)), "line": lineno(off),
                    "chapter": self.ctx["chapter"], "section": self.ctx["section"],
                    "optional": self.ctx["optional"],
                    "statement": statement,
                    "statement_sha256": hashlib.sha256(
                        " ".join(statement.split()).encode()).hexdigest(),
                    "proof_follows": bool(pm), "proof_title": proof_title,
                    "proof_lines": proof.strip().count("\n") + 1 if pm else 0,
                    "outline": bool(re.search(r"outline", proof_title + proof[:400], re.I)),
                    "refs_statement": labels_of(REF.findall(body)),
                    "refs_proof": labels_of(REF.findall(proof)),
                })
                skip_until = after


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("book", type=Path)
    ap.add_argument("number", type=int)
    ap.add_argument("--out", type=Path)
    args = ap.parse_args()
    book = args.book.resolve()
    out = args.out or ROOT / "textbook" / "inventory" / f"edition-{args.number}.json"

    aux = {}
    for line in (book / f"{MAIN}.aux").read_text(errors="ignore").splitlines():
        m = re.match(r"\\newlabel\{([^}@]+)\}\{\{([^}]*)\}\{([^}]*)\}", line)
        if m:
            aux[m.group(1)] = (m.group(2), m.group(3))

    walker = Walker(book)
    walker.walk(book / f"{MAIN}.tex")
    items = walker.items
    mismatched = []
    for it in items:
        if it["label"] in aux:
            number, page = aux[it["label"]]
            if number != it["number"]:
                mismatched.append(f"{it['label']}: counted {it['number']}, the .aux says {number}")
            it["number"], it["page"] = number, page
    if mismatched:
        sys.exit("the count disagrees with the .aux:\n  " + "\n  ".join(mismatched))
    keys = [it["key"] for it in items]
    duplicates = sorted({k for k in keys if keys.count(k) > 1})
    if duplicates:
        sys.exit("two items share a key: " + ", ".join(duplicates))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(items, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    kinds = {}
    for it in items:
        kinds[it["kind"]] = kinds.get(it["kind"], 0) + 1
    unlabelled = [f"{it['number']} {it['title']}" for it in items if not it["label"]]
    print(f"{out.relative_to(ROOT) if out.is_relative_to(ROOT) else out}: {len(items)} items {kinds}")
    print(f"without a label ({len(unlabelled)}): " + "; ".join(unlabelled))


if __name__ == "__main__":
    main()
