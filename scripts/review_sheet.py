#!/usr/bin/env python3
"""A review sheet: the statements that await the author's review, as a PDF.

For each statement the sheet sets side by side:
- the book's statement, typeset with the book's own macros;
- the Lean statement, and every definition of the library it unfolds to;
- the recorded differences from the book (the manifest's fidelity note);
- the two review hashes, which an approval records;
- a box to approve or return it.

  python3 scripts/review_sheet.py [KEY ...] [--report PATH] [--book-aux PATH]

Without keys the sheet holds every statement whose status is stated because
it awaits review, has changed since review, or whose text in the book has
changed. It writes textbook/review/sheet-<date>.tex and .pdf; neither is
committed. The author's decisions are recorded with
`python3 scripts/status.py --approve KEY...`.
"""
import argparse
import datetime
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(1, str(Path(__file__).resolve().parent.parent / "textbook" / "tutorial" / "tools"))
import status  # noqa: E402
from glyphs import literate, unmapped  # noqa: E402

ROOT = status.ROOT
REVIEW = ROOT / "textbook" / "review"
BOOK_STYLE = ROOT / "textbook" / "tutorial" / "tex" / "book"
DEFAULT_AUX = ROOT.parent / "textbook" / "artform-calculus-and-applications.aux"
WAITING = ("awaits review", "changed since review", "the book's text changed since review")

PREAMBLE = r"""\documentclass[11pt,openany]{memoir}
\input{artform-notation}
\input{style}
\usepackage{listings}
%(literate)s
\lstdefinelanguage{Lean}{
  morekeywords={def,abbrev,structure,inductive,class,instance,where,theorem,
    fun,match,with,by,if,then,else,have,let,Type,Prop,True,False},
  sensitive=true, morecomment=[l]{--}, morecomment=[s]{/-}{-/}, morestring=[b]"}
\lstdefinestyle{lean}{language=Lean,style=leanglyphs,
  basicstyle=\ttfamily\fontsize{8.6}{10.4}\selectfont,keywordstyle=\color{ArtBlue},
  commentstyle=\color{ArtGray}\itshape,columns=fixed,basewidth=0.5em,
  keepspaces=true,extendedchars=true,breaklines=true,frame=leftline,
  framerule=1.2pt,rulecolor=\color{ArtTeal},framesep=6pt,xleftmargin=9pt}
\newcommand{\lc}[1]{{\ttfamily\small #1}}
\setsecnumdepth{none}
\begin{document}
\pagestyle{plain}
{\Large\bfseries\color{ArtNavy} Review sheet, %(date)s\par}
\medskip
\noindent %(count)s, from the %(edition)s of the book. For each one, compare
the book's statement with the Lean statement and the definitions it unfolds
to, then mark it approved or returned. An approval is recorded with its two
review hashes, printed under each title: if the Lean statement or one of its
definitions changes later, the statement comes back for review.
"""

ITEM = r"""
\clearpage
\section{%(number)s\quad %(title)s}
\noindent\lc{%(key)s}\quad %(kind)s, tier %(tier)s, batch %(batch)s\\
book source: \lc{%(source)s}\\
review hashes: text \lc{%(text_hash)s}, term \lc{%(term_hash)s}

\subsection*{In the book}
\begin{tcolorbox}[colback=white,colframe=ArtNavy!40,breakable]
%(book)s
\end{tcolorbox}

\subsection*{In Lean}
\begin{lstlisting}[style=lean]
%(lean)s
\end{lstlisting}
%(surface)s
\subsection*{Differences from the book}
%(fidelity)s

\Needspace{5\baselineskip}
\subsection*{Decision}
\noindent$\square$ approved \qquad $\square$ returned:
\hrulefill\par
"""


def escape(s):
    out = []
    for ch in s:
        if ch in "\\":
            out.append(r"\textbackslash{}")
        elif ch in "{}$&#_%":
            out.append("\\" + ch)
        elif ch == "^":
            out.append(r"\^{}")
        elif ch == "~":
            out.append(r"\~{}")
        else:
            out.append(ch)
    return "".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("keys", nargs="*")
    ap.add_argument("--report", type=Path, default=ROOT / "build" / "report.json")
    ap.add_argument("--book-aux", type=Path, default=DEFAULT_AUX)
    ap.add_argument("--date", default=datetime.date.today().isoformat())
    args = ap.parse_args()

    report = status.load_report(args.report)
    edition, inventory = status.load_inventory()
    _, st_entries, def_entries = status.load_manifest()
    results, _, _, _ = status.evaluate(st_entries, def_entries, inventory, report)
    entries = {e["key"]: e for e in st_entries}
    if args.keys:
        chosen = [r for r in results if r["key"] in args.keys]
        unknown = sorted(set(args.keys) - {r["key"] for r in chosen})
        if unknown:
            sys.exit("not statements of the manifest: " + ", ".join(unknown))
    else:
        chosen = [r for r in results if r["status"] == "stated"
                  and any(n in WAITING for n in r["notes"])]
    missing_lean = [r["key"] for r in chosen if r["key"] not in report[0]]
    if missing_lean:
        sys.exit("no Lean statement carries: " + ", ".join(missing_lean))
    if not chosen:
        print("no statement awaits review")
        return 0

    lean_texts = []
    items = []
    for r in chosen:
        st = report[0][r["key"]]
        e = entries[r["key"]]
        book = inventory[r["key"]]["statement"] if inventory and r["key"] in inventory else \
            r"\emph{(the inventory has no text for this statement)}"
        surface = ""
        if st["surface"]:
            surface = "\n\\subsection*{The definitions it unfolds to}\n" + "".join(
                "\\begin{lstlisting}[style=lean]\n%s\n\\end{lstlisting}\n" % s for s in st["surface"])
        lean_texts += [st["text"], *st["surface"]]
        items.append(ITEM % {
            "number": r["number"], "title": r["title"], "key": escape(r["key"]),
            "kind": e.get("kind", ""), "tier": r["tier"], "batch": r["batch"],
            "source": escape(e.get("source", "")), "book": book, "lean": st["text"],
            "surface": surface,
            "fidelity": escape(e.get("fidelity", "").strip()) or r"\emph{None recorded.}",
            "text_hash": status.text_hash(st)[:12], "term_hash": status.term_hash(st)[:12],
        })
    missing = unmapped(lean_texts)
    if missing:
        sys.exit("no glyph for: " + " ".join(missing) +
                 " (add them to textbook/tutorial/tools/glyphs.py)")
    edition_name = (f"{status.ordinal(edition['number'])} edition" if edition else "current edition")
    count = f"{len(items)} statement" + ("s" if len(items) != 1 else "")
    tex = PREAMBLE % {"literate": literate(lean_texts), "date": args.date,
                      "count": count, "edition": edition_name}
    tex += "".join(items) + "\n\\end{document}\n"

    REVIEW.mkdir(parents=True, exist_ok=True)
    name = f"sheet-{args.date}"
    (REVIEW / f"{name}.tex").write_text(tex, encoding="utf-8")
    labels = []
    if args.book_aux.exists():
        labels = [ln for ln in args.book_aux.read_text(errors="replace").splitlines()
                  if ln.startswith("\\newlabel")]
    else:
        print(f"warning: {args.book_aux} not found; the book's references print as ??")
    env = dict(os.environ, TEXINPUTS=f".:{BOOK_STYLE}//:")
    aux = REVIEW / f"{name}.aux"
    aux.unlink(missing_ok=True)
    for _ in range(2):
        if aux.exists() and labels:
            with aux.open("a") as f:
                f.write("\n".join(labels) + "\n")
        subprocess.run(["pdflatex", "-interaction=nonstopmode", f"{name}.tex"],
                       cwd=REVIEW, env=env, capture_output=True)
    log = (REVIEW / f"{name}.log").read_text(errors="replace")
    errors = [ln for ln in log.splitlines() if ln.startswith("!")]
    for ln in errors[:10]:
        print(ln)
    print(f"{REVIEW.relative_to(ROOT)}/{name}.pdf: {count}; LaTeX errors: {len(errors)}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
