# Artform Calculus: proofs in Lean

Lean 4 proofs of the theorems of the textbook *Artform Calculus*, and a guide
to reading them.

**Start here:** [Lean through Artform Calculus](textbook/lean-through-artform-calculus.pdf)
(PDF). It teaches Lean from the beginning and writes the constructions of
Chapter 1 of the book in Lean.

**This repository is being set up.** No statement is formalized yet.

## What will be proved

Every numbered theorem, proposition, lemma and corollary of *Artform
Calculus* that [`textbook/STATUS.md`](textbook/STATUS.md) marks **proved**
has a Lean statement, which the author reviewed against the book. It also has
a proof that Lean's kernel checks using only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

<!-- status:begin -->
| Status | Statements |
|---|---|
| proved | 0 |
| partial | 0 |
| stated | 35 |
| planned | 68 |
| informal | 0 |
| **total** | **103** |
<!-- status:end -->

Lean checks proofs, not the choice of a model. The repository does not claim
that a physical model describes nature, or that one reading of an artform is
the right one.

## Build

You need [elan](https://github.com/leanprover/elan) and git.

    git clone https://github.com/skrivov/artform-calculus-proofs
    cd artform-calculus-proofs
    lake exe cache get      # Mathlib's compiled files: a few GB
    lake build

## Layout

- `textbook/`: the textbook's definitions, statements and proofs, in the Lean
  library `ArtformTextbook`, with the status table; and the guide, whose Lean
  files and LaTeX sources are in `textbook/tutorial/`.
- `scripts/`: the status report and the checks that CI runs.

## Licence

Lean code and scripts: Apache-2.0 ([LICENSE](LICENSE)). The guide and its
LaTeX sources: CC BY 4.0 ([textbook/tutorial/tex/LICENSE](textbook/tutorial/tex/LICENSE)).
The book's statement texts will be under CC BY 4.0 too.
