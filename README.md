# Artform Calculus: proofs in Lean

Lean 4 proofs of the theorems of the textbook *Artform Calculus*, and a guide
to reading them.

**Start here:** [Lean through Artform Calculus](textbook/lean-through-artform-calculus.pdf)
(PDF). It teaches Lean from the beginning, writes the constructions of
Chapter 1 of the book in Lean, and then presents this repository, reading
four of its statements closely.

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
| proved | 91 |
| partial | 2 |
| stated | 8 |
| planned | 2 |
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
The book's statement texts, quoted in `textbook/inventory/`: CC BY 4.0.
