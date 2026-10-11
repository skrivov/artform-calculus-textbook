# The textbook in Lean

This folder holds the Lean statements and proofs of the numbered statements
of *Artform Calculus*. The tutorial that teaches how to read them is in
[`../tutorial/`](../tutorial/README.md).

- `ArtformTextbook/`: the library. Part III of the tutorial quotes some of its
  files, between `-- ANCHOR:` comments.
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
- `review/`: the independent audit and the approval log. The
  [11 October 2026 audit](review/audit-2026-10-11.md) gives a verdict for all
  103 statements and explains the six returned translations. Review sheets
  (`scripts/review_sheet.py`) are written here but not committed.
- `FINDINGS.md`: errors or gaps found in the book while formalizing it.
- `PILOT.md`: what the first 15 statements cost, and the order and
  decisions that follow from them.

Each chapter has a folder `ArtformTextbook/ChNN/` with:
- `Defs/`: the book's definitions;
- `Statements.lean`, or `Statements/` when a chapter has several topics: the
  statements, as propositions;
- the proofs;
- `Examples.lean`: the book's running examples.
