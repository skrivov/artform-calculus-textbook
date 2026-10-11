# The textbook in Lean

This folder holds the Lean statements and proofs of the numbered statements
of *Artform Calculus*, and the guide *Lean through Artform Calculus*.

- `lean-through-artform-calculus.pdf`: the guide. Part I teaches the basics
  of Lean; Part II writes the constructions of Chapter 1 of the book in Lean.
- `tutorial/`: the guide's Lean files (`LeanBasics.lean`,
  `ArtformChapter1.lean`, checked on every build), copies without the checks
  for an editor (`play/`), the LaTeX sources (`tex/`) and `build.sh`.
- `ArtformTextbook/`: the library.
  - `Meta/Book.lean` defines the attribute `@[book "label"]`, which ties a
    Lean declaration to the statement or definition of the book with that
    label.
  - It also defines the command `#book "label"`, which lists those
    declarations.
- `edition.toml`: the edition of the book this folder follows (the 52nd).
- `inventory/edition-52.json`: the book's 103 numbered statements and 92
  definitions as the book prints them, with a hash of each statement
  (`scripts/book_inventory.py`).
- `manifest.toml`: one entry per statement and definition, with its Lean
  names, status, review and differences from the book. Each statement also
  has a tier (A elementary, B structural, C Mathlib theory, D certified
  computation, E research or modelling) and the batch it belongs to.
- `STATUS.md`: the status table, generated from the manifest by
  `scripts/status.py`.
- `review/`: the author's review log. Review sheets
  (`scripts/review_sheet.py`) are written here but not committed.
- `FINDINGS.md`: errors or gaps found in the book while formalizing it.

Each chapter will get a folder `ArtformTextbook/ChNN/` with:
- `Defs/`: the book's definitions;
- `Statements.lean`: the statements, as propositions;
- the proofs;
- `Examples.lean`: the book's running examples.
