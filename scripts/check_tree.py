#!/usr/bin/env python3
"""Checks on the repository's files.

Fails when:
  - a Lean file of the libraries (textbook/ArtformTextbook/, scores/ArtformScores/)
    contains, outside comments and strings, one of the words FORBIDDEN, or declares
    an axiom;
  - any file contains an absolute home path or an e-mail address other than a
    GitHub no-reply address;
  - a file other than the guide's PDF is larger than 5 MB;
  - PLAN.md or plan/ is tracked (they stay on the author's machine);
and, with --identity, when this repository's commit e-mail, or the author
e-mail of any commit, is not a GitHub no-reply address.

The files checked are those git tracks, plus new files it does not ignore.
Usage, from the repository root:  python3 scripts/check_tree.py [--identity]
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIBRARY = ("textbook/ArtformTextbook/", "scores/ArtformScores/")
GUIDE_PDF = "tutorial/lean-through-artform-calculus.pdf"
LIMIT = 5 * 1024 * 1024
FORBIDDEN = ("sorry", "admit", "native_decide", "implemented_by", "extern",
             "unsafe", "debug.skipKernelTC")
# Patterns are assembled from pieces, so that this file does not match itself.
HOME = "/" + "home" + "/"
EMAIL = re.compile(r"[A-Za-z0-9._%+-]+" + "@" + r"[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)*\.[A-Za-z]{2,}")
NOREPLY = "@" + "users.noreply.github.com"
AXIOM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*axiom\b",
                   re.MULTILINE)
IDENT = re.compile(r"[A-Za-z0-9_'!?Ͱ-Ͽἀ-῿₀-ₜ\U0001d49c-\U0001d59f]")


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True,
                          check=True).stdout


def files():
    names = git("ls-files", "-z", "--cached", "--others", "--exclude-standard").split("\0")
    return sorted({n for n in names if n and (ROOT / n).is_file()})


def lean_code(text):
    """The text with comments, string literals and char literals blanked."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append("\n" * text.count("\n", i, j))
            i = j
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(" ")
            i = j + 1
        elif text[i] == "'" and (i == 0 or not IDENT.match(text[i - 1])):
            m = re.match(r"'(?:\\.|[^\\'])'", text[i:])
            out.append(" " if m else "'")
            i += len(m.group(0)) if m else 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main():
    problems = []
    for name in files():
        path = ROOT / name
        if name == "PLAN.md" or name.startswith("plan/"):
            problems.append(f"{name}: the plan must stay out of git")
        size = path.stat().st_size
        if size > LIMIT and name != GUIDE_PDF:
            problems.append(f"{name}: {size / 2**20:.1f} MB, over the 5 MB limit")
        data = path.read_bytes()
        if b"\0" in data[:8192]:
            continue
        text = data.decode("utf-8", errors="replace")
        if HOME in text:
            problems.append(f"{name}: contains an absolute home path")
        for m in EMAIL.finditer(text):
            if not m.group(0).endswith(NOREPLY):
                problems.append(f"{name}: contains an e-mail address")
                break
        if name.startswith(LIBRARY) and name.endswith(".lean"):
            code = lean_code(text)
            for word in FORBIDDEN:
                for m in re.finditer(r"(?<![\w.])" + re.escape(word) + r"(?![\w])", code):
                    line = code.count("\n", 0, m.start()) + 1
                    problems.append(f"{name}:{line}: uses `{word}`")
            for m in AXIOM.finditer(code):
                line = code.count("\n", 0, m.start()) + 1
                problems.append(f"{name}:{line}: declares an axiom")

    if "--identity" in sys.argv[1:]:
        try:
            email = git("config", "user.email").strip()
        except subprocess.CalledProcessError:
            email = ""
        if not email.endswith(NOREPLY):
            problems.append("git config user.email is not a GitHub no-reply address")
        try:
            authors = set(git("log", "--format=%ae").split())
        except subprocess.CalledProcessError:
            authors = set()           # no commit yet
        for a in sorted(authors):
            if not a.endswith(NOREPLY):
                problems.append("a commit has an author e-mail that is not a GitHub no-reply address")
                break

    for p in problems:
        print(f"problem: {p}")
    print(f"{len(files())} files checked; {len(problems)} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
