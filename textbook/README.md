# The textbook in Lean

This folder holds the Lean statements and proofs of the numbered statements
of *Artform Calculus*. The guide *Lean through Artform Calculus* will join
them here.

- `ArtformTextbook/`: the library.
  - `Meta/Book.lean` defines the attribute `@[book "label"]`, which ties a
    Lean declaration to the statement or definition of the book with that
    label.
  - It also defines the command `#book "label"`, which lists those
    declarations.
- `manifest.toml`: one entry per statement and definition of the book, with
  its Lean names, status and review. It is empty for now.
- `STATUS.md`: the status table, generated from the manifest by
  `scripts/status.py`.

Each chapter will get a folder `ArtformTextbook/ChNN/` with:
- `Defs/`: the book's definitions;
- `Statements.lean`: the statements, as propositions;
- the proofs;
- `Examples.lean`: the book's running examples.
