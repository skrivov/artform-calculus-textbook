# Artform Calculus: proofs in Lean

This repository accompanies the textbook *Artform Calculus*. It holds three
things.

- **The textbook's theorems in Lean** ([`textbook/`](textbook/README.md)): a
  Lean statement of each numbered theorem, proposition, lemma and corollary of
  the book, with proofs that Lean's kernel checks.
- **The Lean tutorial** ([`tutorial/`](tutorial/README.md)):
  [*Lean through Artform Calculus*](tutorial/lean-through-artform-calculus.pdf)
  (PDF). It teaches Lean from the beginning, writes the constructions of
  Chapter 1 of the book in Lean, and then presents this repository, reading
  four of its statements closely. Start here.
- **The type theory of the five roles** ([`type-theory/`](type-theory/README.md)):
  the paper [*Five Roles for Artforms*](type-theory/paper/role-stratified-artform-type-theory.pdf),
  on the role-based type theory the book uses, and the Lean library
  `ArtformRoles` that checks its first part.

**Work in progress.** The [independent review of 11 October 2026](textbook/review/audit-2026-10-11.md)
records a verdict for every numbered statement. Six existing translations
need revision, two approved translations still need proofs, and two statements
remain planned. The two *partial* approvals cover only the scope recorded in
their fidelity notes. A statement becomes *proved* only when its translation
has passed review against the book and Lean has checked its proof. Errors and
gaps found in the book while formalizing it are recorded in
[`textbook/FINDINGS.md`](textbook/FINDINGS.md).

## What will be proved

Every numbered theorem, proposition, lemma and corollary of *Artform
Calculus* that [`textbook/STATUS.md`](textbook/STATUS.md) marks **proved**
has a Lean statement, which an independent review checked against the book. It also has
a proof that Lean's kernel checks using only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

<!-- status:begin -->
| Status | Statements |
|---|---|
| proved | 0 |
| partial | 0 |
| stated | 101 |
| planned | 2 |
| informal | 0 |
| **total** | **103** |
<!-- status:end -->

Lean checks proofs, not the choice of a model. The repository does not claim
that a physical model describes nature, or that one reading of an artform is
the right one.

**Which edition of the book.** The repository follows the 54th edition, of
11 October 2026 (`textbook/edition.toml`), the first to cite this repository.
It prints the same 103 statements and 92 definitions as the 52nd edition,
word for word, and gives labels to seventeen items that had none.

## Build

You need [elan](https://github.com/leanprover/elan) and git.

    git clone https://github.com/skrivov/artform-calculus-textbook
    cd artform-calculus-textbook
    lake exe cache get      # Mathlib's compiled files: a few GB
    lake build

Publication checks run locally; GitHub Actions is disabled for this repository.

    lake build --wfail
    mkdir -p build
    lake env lean --run scripts/Report.lean > build/report.json
    python3 scripts/status.py --check
    python3 scripts/check_tree.py --identity
    python3 -m unittest discover -s scripts/tests
    python3 tutorial/tools/extract_listings.py --check

The tutorial's PDF is rebuilt with `bash tutorial/build.sh`, and the paper's
with `latexmk -pdf` in `type-theory/paper/`.

## Layout

- `textbook/`: the textbook's definitions, statements and proofs, in the Lean
  library `ArtformTextbook`; the manifest and the status table; the inventory
  of the book's statements; the independent review; and the findings.
- `tutorial/`: the tutorial *Lean through Artform Calculus*: its PDF, its
  LaTeX sources, and its Lean files, the library `Tutorial`.
- `type-theory/`: the paper *Five Roles for Artforms*, which asks whether the
  book's five roles are the right ones, and the Lean library `ArtformRoles`
  that checks its first part.
- `scripts/`: the status report and local publication checks.

## Licence

Lean code and scripts: Apache-2.0 ([LICENSE](LICENSE)). The tutorial and its
LaTeX sources: CC BY 4.0 ([tutorial/tex/LICENSE](tutorial/tex/LICENSE)).
The book's statement texts, quoted in `textbook/inventory/`: CC BY 4.0.
The type-theory paper and its LaTeX sources: CC BY 4.0
([type-theory/paper/LICENSE](type-theory/paper/LICENSE)).
