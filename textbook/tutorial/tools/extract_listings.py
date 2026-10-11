#!/usr/bin/env python3
"""Cut the printed Lean listings of the guide "Lean through Artform Calculus"
out of the files Lean checks: LeanBasics.lean (Part I), ArtformChapter1.lean
(Part II) and RepositoryTour.lean (Part III), in textbook/tutorial/, and the
library's own files under textbook/ArtformTextbook/ (Part III), where the
anchors are plain comments and docstrings are left out of the listing.

  -- ANCHOR: name ... -- ANCHOR_END: name   one listing -> tex/generated/snippets/name.lean
  ... -- HIDE                               a line Lean needs and the page omits
  ... -- PROOF  ...  -- QED                  a routine part, printed as gray dots
  /-- info: x -/ #guard_msgs in              Lean's one-line answer, printed as a
                                             comment `-- x` after the next line
  /-- info: ... -/  (several lines or        printed as "Lean replies" (name.info),
  messages, or one line too long to follow   one message per line
  the code)
  /-- error: ... -/                          printed as "Lean refuses it" (name.msg)

A statement of the book quoted by \\bookstatement{label} in the guide's LaTeX
is written to snippets/book-statements.tex, as a macro, from the inventory of
the edition the repository follows (textbook/edition.toml), so that the quote
is the book's text, number and title.

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
import json
import re
import tomllib
import sys
import tempfile
from pathlib import Path

TUTORIAL = Path(__file__).resolve().parent.parent
TEX = TUTORIAL / "tex"
SOURCES = [TUTORIAL / "LeanBasics.lean",
           TUTORIAL / "ArtformChapter1.lean",
           TUTORIAL / "RepositoryTour.lean"]
LIBRARY = TUTORIAL.parent / "ArtformTextbook"
OUT = TEX / "generated" / "snippets"
DRAFTS = [TEX / "part1-basics.tex",
          TEX / "part2-chapter1.tex",
          TEX / "part3-repository.tex"]
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


def messages(raw):
    """The kind and the text of a #guard_msgs block; several messages, which
    Lean separates by a line ---, are joined one per line."""
    parts = raw.split("\n---\n")
    kind = parts[0].partition(":")[0]
    texts = [p.partition(":")[2].strip("\n").lstrip(" ") for p in parts]
    return kind, "\n".join(texts)


def listing(lines, i, name, library=False):
    """Read one anchor from line i; return its printed lines, each with the
    one-line answer that belongs to it, its messages, and the next index.
    In a library file a docstring is a comment for the reader of the file, and
    the listing leaves it out."""
    body, info, error = [], None, None
    pending = None                      # a one-line answer for the next line
    while not lines[i].lstrip().startswith(f"-- ANCHOR_END: {name}"):
        ln = lines[i]
        if library and ln.lstrip().startswith(("/--", "/-!")):
            while not lines[i].rstrip().endswith("-/"):
                i += 1
            i += 1
            continue
        if ln.startswith("/--"):
            j = i
            while not lines[j].rstrip().endswith("-/"):
                j += 1
            raw = "\n".join(lines[i:j + 1])[3:-2].strip()
            assert lines[j + 1].startswith("#guard_msgs"), name
            kind, text = messages(raw)
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
        if pending is not None and len(ln.rstrip()) + 5 + len(pending) > WIDTH:
            info, pending = pending, None   # too long to follow the code
        body.append((ln.rstrip(), pending))
        pending = None
        i += 1
    return body, info, error, i + 1


def dedent(body):
    """Remove the indentation that every printed line of a listing shares."""
    widths = [len(code) - len(code.lstrip()) for code, _ in body if code.strip()]
    cut = min(widths, default=0)
    return [(code[cut:], ans) for code, ans in body]


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


def library_sources():
    """The library's files that hold an anchor, in a fixed order."""
    return [f for f in sorted(LIBRARY.rglob("*.lean"))
            if "-- ANCHOR: " in f.read_text(encoding="utf-8")]


def extract(out: Path, quiet: bool = False) -> int:
    sources = [(src, False) for src in SOURCES] + [(src, True) for src in library_sources()]
    out.mkdir(parents=True, exist_ok=True)
    for old in out.glob("*"):
        old.unlink()

    names, sizes, written = [], {}, []
    for src, library in sources:
        lines = src.read_text(encoding="utf-8").split("\n")
        i = 0
        while i < len(lines):
            m = re.match(r"\s*-- ANCHOR: (\S+)$", lines[i])
            if not m:
                i += 1
                continue
            name = m.group(1)
            assert name not in names, f"duplicate listing {name}"
            names.append(name)
            body, info, error, i = listing(lines, i + 1, name, library)
            if library:
                body = dedent(body)
            printed = render(body)
            long = [ln for ln in printed if len(ln) > WIDTH]
            if long:
                print(f"{name}: {len(long)} line(s) over {WIDTH} characters")
            sizes[name] = len(printed)
            files = [(f"{name}.lean", "\n".join(printed))]
            if info is not None:
                files.append((f"{name}.info", info))
            if error is not None:
                files.append((f"{name}.msg", error))
            for fname, text in files:
                (out / fname).write_text(text + "\n", encoding="utf-8")
                written.append(text)
    # Inline code in the text (\li!...!) is printed with the same glyphs.
    for d in DRAFTS:
        written += re.findall(r"\\li!([^!]*)!", d.read_text(encoding="utf-8"))
    missing = unmapped(written)
    if missing:
        print("no glyph for:", " ".join(missing))
        return 1

    (out / "sizes.tex").write_text(
        "% generated: printed lines per listing\n" + "".join(
            "\\expandafter\\def\\csname leanlines@%s\\endcsname{%d}\n" % kv
            for kv in sizes.items()), encoding="utf-8")
    (out / "literate.tex").write_text(
        "% generated by tools/extract_listings.py\n" + literate(written),
        encoding="utf-8")

    if write_book_statements(out):
        return 1

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


def write_book_statements(out: Path) -> int:
    """Write each statement of the book that the guide quotes."""
    wanted = set()
    for d in DRAFTS:
        wanted |= set(re.findall(r"\\bookstatement\{([^}]+)\}", d.read_text(encoding="utf-8")))
    out_file = out / "book-statements.tex"
    if not wanted:
        out_file.write_text("% generated by tools/extract_listings.py: no quotes\n",
                            encoding="utf-8")
        return 0
    textbook = TUTORIAL.parent
    edition = tomllib.loads((textbook / "edition.toml").read_text(encoding="utf-8"))
    inventory = json.loads((textbook / edition["inventory"]).read_text(encoding="utf-8"))
    items = {it["label"]: it for it in inventory if it.get("label")}
    missing = sorted(wanted - set(items))
    if missing:
        print("not in the inventory:", ", ".join(missing))
        return 1
    defs = ["% generated by tools/extract_listings.py: the statements the guide quotes"]
    for label in sorted(wanted):
        it = items[label]
        # A removed \label can leave a blank line inside a display.
        text = re.sub(r"\n[ \t]*\n", "\n", it["statement"].strip())
        defs.append("\\expandafter\\def\\csname bookstmt@%s\\endcsname{%%\n"
                    "\\begin{bookquote}{%s %s}{%s}\n%s\n\\end{bookquote}}"
                    % (label, it["kind"].capitalize(), it["number"], it["title"], text))
    out_file.write_text("\n".join(defs) + "\n", encoding="utf-8")
    return 0


def inputs_hash(snippets: Path) -> str:
    """One hash of everything the PDF is made from: the snippets, the guide's
    LaTeX, its bibliography, the book's style files and numbers, and the
    sources of its generated status appendix. That appendix is not committed,
    so hash its tracked inputs rather than a possibly missing or stale copy.
    CI checks the manifest against the current Lean report separately.
    """
    files = sorted(snippets.glob("*")) + sorted(TEX.glob("*.tex")) + \
        sorted(TEX.glob("*.bib")) + sorted((TEX / "book").glob("*.tex")) + \
        sorted((TEX / "generated").glob("book-*.tex"))
    h = hashlib.sha256()
    for f in files:
        rel = f.name if f.parent == snippets else str(f.relative_to(TEX))
        h.update(rel.encode() + b"\0" + f.read_bytes() + b"\0")
    textbook = TUTORIAL.parent
    edition = tomllib.loads((textbook / "edition.toml").read_text(encoding="utf-8"))
    status_inputs = [textbook / "manifest.toml", textbook / "edition.toml",
                     textbook / edition["inventory"], textbook.parent / "scripts" / "status.py"]
    for f in status_inputs:
        h.update(str(f.relative_to(textbook.parent)).encode() + b"\0" + f.read_bytes() + b"\0")
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
