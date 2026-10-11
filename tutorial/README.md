# Lean through Artform Calculus

The tutorial [*Lean through Artform Calculus*](lean-through-artform-calculus.pdf)
(PDF), an introduction to Lean and to the textbook's proofs.

- Part I teaches the basics of Lean.
- Part II writes the constructions of Chapter 1 of the book in Lean, in core
  Lean, in one file.
- Part III presents this repository: what it proves, how a statement of the
  book is written in Lean, four statements read closely from the book's words
  to their proofs, and the checks the repository makes on itself.

## Files

- `LeanBasics.lean`, `ArtformChapter1.lean`, `RepositoryTour.lean`: the
  tutorial's Lean files, the library `Tutorial`. Every answer of Lean that the
  tutorial quotes is pinned there with `#guard_msgs`, so building the library
  checks the tutorial.
- `play/`: copies of the first two files without the checks, which show every
  answer in an editor (`tools/make_play_copies.py`).
- `tex/`: the LaTeX sources, in the book's style (`tex/book/`).
- `tools/`: `extract_listings.py` cuts the printed listings from the Lean
  files and checks that the PDF is built from the current sources;
  `glyphs.py` says how each non-ASCII character is printed.
- `build.sh`: builds the PDF.

## Build

From the repository root, with `~/.elan/bin` on `PATH`:

    bash tutorial/build.sh

The PDF and its LaTeX sources are licensed CC BY 4.0 ([tex/LICENSE](tex/LICENSE));
the Lean files are code, under the repository's Apache-2.0 licence.
