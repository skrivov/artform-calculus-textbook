# Artform Calculus: proofs in Lean

Lean 4 proofs of the theorems of the textbook *Artform Calculus*, and a guide
to reading them.

**This repository is being set up.** No statement is formalized yet. The
guide, *Lean through Artform Calculus*, and the statement table come next.

## What will be proved

Every numbered theorem, proposition, lemma and corollary of *Artform
Calculus* that [`textbook/STATUS.md`](textbook/STATUS.md) marks **proved**
has a Lean statement, which the author reviewed against the book. It also has
a proof that Lean's kernel checks using only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

<!-- status:begin -->
No statement is recorded yet.
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
  library `ArtformTextbook`, with the status table.
- `scripts/`: the status report and the checks that CI runs.

## Licence

Lean code and scripts: Apache-2.0 ([LICENSE](LICENSE)). The guide and the
book's statement texts will be under CC BY 4.0.
