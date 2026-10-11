# Rules for agents in this repository

This repository holds Lean proofs of the numbered statements of the textbook
*Artform Calculus*. These rules apply to every change.

## How the book is written in Lean

- Every definition is in namespace `Artform`.
- A statement of the book is a `def … : Prop` in namespace `Artform.Statement`,
  in the chapter's `Statements.lean`. It is tagged with the book's label, for
  example `@[book "thm:noether"]`.
- Its proof is a `theorem` in the same chapter folder, with the same tag,
  whose type is exactly that statement:
  `@[book "thm:noether"] theorem noether : Statement.noether := …`.
- A definition of the book can be tagged the same way, for example
  `@[book "def:canvas"]`.
- Each docstring opens with the book's number and title:
  `/-- **Theorem 5.6** (Noether's theorem for affine laws). … -/`.
- Labels, not numbers, tie Lean to the book: numbers change between
  editions, and labels do not.
- Chapter folders `Ch01`–`Ch13` follow the book's chapters. Each one holds
  `Defs/`, `Statements.lean`, the proofs, and `Examples.lean`.

## Rules

1. Read `textbook/manifest.toml` and `textbook/STATUS.md` before starting;
   every statement's state is there. If `PLAN.md` exists, read it too. It is
   kept out of git on the author's machine.
2. A change to a file in a `Defs/` folder or to a `Statements.lean` must be
   named in the commit message, together with the entries it sends back to
   review. `scripts/status.py` resets those reviews in any case.
3. Never weaken a statement, add a hypothesis, or narrow a definition to make
   a proof go through. If a statement cannot be proved as the book prints it,
   record it in `textbook/FINDINGS.md` and stop work on that statement.
4. The library contains no `sorry`, `admit`, `native_decide`, new `axiom`s,
   `implemented_by`, `extern` or `unsafe`. Large computations use
   certificates and `decide +kernel`.
5. Proofs may be written by any means. A statement counts only once the
   author has approved it. Approval is recorded by
   `python3 scripts/status.py --approve <key>`, run only on the author's
   instruction.
6. Every proved statement has a non-vacuity example on the book's running
   example: an `example` showing that the statement's hypotheses can be met,
   in a section `Non-vacuity` at the end of its proof file.
7. Before every commit, run the four commands below, with `~/.elan/bin` on
   `PATH`. Write commit messages in the imperative.

       lake build --wfail
       mkdir -p build && lake env lean --run scripts/Report.lean > build/report.json
       python3 scripts/status.py --check
       python3 scripts/check_tree.py --identity

8. Until the author says otherwise, pushing to GitHub needs the author's
   go-ahead in chat. For this repository, this replaces the workspace rule
   that a completed change is published at once.
9. Do not edit the textbook from this repository. A change to the book goes
   through the book's own process.
10. Scripts are Python with the standard library only.
