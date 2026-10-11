#!/usr/bin/env python3
"""Cut the printed Lean listings of the guide "Lean through Artform Calculus"
out of the files Lean checks: LeanBasics.lean (Part I) and
ArtformChapter1.lean (Part II), in textbook/tutorial/.

  -- ANCHOR: name ... -- ANCHOR_END: name   one listing -> tex/generated/snippets/name.lean
  ... -- HIDE                               a line Lean needs and the page omits
  ... -- PROOF  ...  -- QED                  a routine part, printed as gray dots
  /-- info: x -/ #guard_msgs in              Lean's one-line answer, printed as a
                                             comment `-- x` after the next line
  /-- info: ... -/  (several lines)          printed as "Lean replies" (name.info)
  /-- error: ... -/                          printed as "Lean refuses it" (name.msg)

Blank lines inside a listing are dropped: declarations are told apart by
their keyword at the margin. Also writes snippets/literate.tex (one glyph per
non-ASCII character; an unmapped character stops the run) and
snippets/sizes.tex (printed lines per listing), and fails when the guide
cites a listing that does not exist.

  python3 tools/extract_listings.py           write the snippets
  python3 tools/extract_listings.py --hash    print the hash of every input of
                                              the guide (build.sh stores it in
                                              tex/generated/inputs.sha256)
  python3 tools/extract_listings.py --check   fail if that hash differs from the
                                              stored one: the committed PDF is
                                              then not built from these sources
"""
import hashlib
import re
import sys
import tempfile
from pathlib import Path

TUTORIAL = Path(__file__).resolve().parent.parent
TEX = TUTORIAL / "tex"
SOURCES = [TUTORIAL / "LeanBasics.lean",
           TUTORIAL / "ArtformChapter1.lean"]
OUT = TEX / "generated" / "snippets"
DRAFTS = [TEX / "part1-basics.tex",
          TEX / "part2-chapter1.tex"]
STORED = TEX / "generated" / "inputs.sha256"
WIDTH = 76      # printed characters per code line

# How listings prints each non-ASCII character: the table shared with the
# review sheets (glyphs.py). Only the characters the sources use are written.
from glyphs import GLYPHS, literate, unmapped  # noqa: E402

ELIDED = "⋯"


def elide(line: str) -> str:
    head = line.split("-- PROOF")[0].rstrip()
    if head.endswith(","):
        return head + " " + ELIDED + "⟩"
    if head.endswith(" by"):
        return head[: -len(" by")] + " " + ELIDED
    if head.endswith(":="):
        return head + " " + ELIDED
    return head + " := " + ELIDED


def listing(lines, i, name):
    """Read one anchor from line i; return its printed lines, each with the
    one-line answer that belongs to it, its messages, and the next index."""
    body, info, error = [], None, None
    pending = None                      # a one-line answer for the next line
    while not lines[i].startswith(f"-- ANCHOR_END: {name}"):
        ln = lines[i]
        if ln.startswith("/--"):
            j = i
            while not lines[j].rstrip().endswith("-/"):
                j += 1
            raw = "\n".join(lines[i:j + 1])[3:-2].strip()
            assert lines[j + 1].startswith("#guard_msgs"), name
            kind, _, text = raw.partition(":")
            text = text.strip("\n").lstrip(" ")
            if kind == "info" and "\n" not in text:
                pending = text
            elif kind == "info":
                info = text
            else:
                error = text
            i = j + 2
            continue
        if ln.rstrip().endswith("-- HIDE") or not ln.strip():
            i += 1
            continue
        if "-- PROOF" in ln:
            body.append((elide(ln), None))
            while "-- QED" not in lines[i]:
                i += 1
            i += 1
            continue
        body.append((ln.rstrip(), pending))
        pending = None
        i += 1
    return body, info, error, i + 1


def render(body):
    """Align the inline answers of one listing in one column."""
    answered = [len(code) for code, ans in body if ans is not None]
    col = max(answered) + 2 if answered else 0
    out = []
    for code, ans in body:
        if ans is None:
            out.append(code)
        else:
            pad = col if col + 3 + len(ans) <= WIDTH else len(code) + 2
            out.append(code.ljust(pad) + "-- " + ans)
    return out


def extract(out: Path, quiet: bool = False) -> int:
    texts = [src.read_text(encoding="utf-8") for src in SOURCES]
    missing = unmapped(texts)
    if missing:
        print("no glyph for:", " ".join(missing))
        return 1
    out.mkdir(parents=True, exist_ok=True)
    for old in out.glob("*"):
        old.unlink()

    names, sizes = [], {}
    for text in texts:
        lines = text.split("\n")
        i = 0
        while i < len(lines):
            m = re.match(r"-- ANCHOR: (\S+)$", lines[i])
            if not m:
                i += 1
                continue
            name = m.group(1)
            assert name not in names, f"duplicate listing {name}"
            names.append(name)
            body, info, error, i = listing(lines, i + 1, name)
            printed = render(body)
            long = [ln for ln in printed if len(ln) > WIDTH]
            if long:
                print(f"{name}: {len(long)} line(s) over {WIDTH} characters")
            sizes[name] = len(printed)
            (out / f"{name}.lean").write_text("\n".join(printed) + "\n", encoding="utf-8")
            if info is not None:
                (out / f"{name}.info").write_text(info + "\n", encoding="utf-8")
            if error is not None:
                (out / f"{name}.msg").write_text(error + "\n", encoding="utf-8")

    (out / "sizes.tex").write_text(
        "% generated: printed lines per listing\n" + "".join(
            "\\expandafter\\def\\csname leanlines@%s\\endcsname{%d}\n" % kv
            for kv in sizes.items()), encoding="utf-8")
    (out / "literate.tex").write_text(
        "% generated by tools/extract_listings.py\n" + literate(texts),
        encoding="utf-8")

    cited = set()
    for d in DRAFTS:
        cited |= set(re.findall(r"\\lean(?:listing|message|reply)\{([^}]+)\}",
                                d.read_text(encoding="utf-8")))
    absent = sorted(cited - set(names))
    unused = sorted(set(names) - cited)
    if not quiet:
        print(f"{len(names)} listings extracted; cited {len(cited)}")
        if unused:
            print("not printed:", ", ".join(unused))
    if absent:
        print("cited but absent:", ", ".join(absent))
        return 1
    return 0


def inputs_hash(snippets: Path) -> str:
    """One hash of everything the PDF is made from: the snippets, the guide's
    LaTeX, its bibliography, the book's style files and numbers."""
    files = sorted(snippets.glob("*")) + sorted(TEX.glob("*.tex")) + \
        sorted(TEX.glob("*.bib")) + sorted((TEX / "book").glob("*.tex")) + \
        sorted((TEX / "generated").glob("book-*.tex"))
    h = hashlib.sha256()
    for f in files:
        rel = f.name if f.parent == snippets else str(f.relative_to(TEX))
        h.update(rel.encode() + b"\0" + f.read_bytes() + b"\0")
    return h.hexdigest()


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] in ("--hash", "--check"):
        with tempfile.TemporaryDirectory() as tmp:
            if extract(Path(tmp), quiet=True):
                return 1
            digest = inputs_hash(Path(tmp))
        if sys.argv[1] == "--hash":
            print(digest)
            return 0
        stored = STORED.read_text().strip() if STORED.exists() else "(none)"
        if digest != stored:
            print("the guide's sources changed since the PDF was built: "
                  "run textbook/tutorial/build.sh and commit the PDF")
            return 1
        print("the guide's PDF is built from the current sources")
        return 0
    return extract(OUT)


if __name__ == "__main__":
    sys.exit(main())
