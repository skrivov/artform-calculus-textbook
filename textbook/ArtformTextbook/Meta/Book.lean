import Lean

/-!
# Ties to the textbook

`@[book "label"]` ties a declaration to the statement or definition of the
textbook that carries that `\label`:

* on a `def … : Prop` in `Artform.Statement`, it marks the Lean form of a
  numbered statement, which the author reviews against the book;
* on a `theorem`, it marks the proof of that statement;
* on any other declaration, it marks the Lean form of a book definition.

`#book "label"` lists the declarations tied to a label. `scripts/Report.lean`
lists all of them, and `scripts/status.py` checks that each proof proves
exactly the statement with its label.
-/

namespace Artform
open Lean Elab Command

/-- `@[book "label"]`: the textbook label of the statement or definition that
this declaration states, proves or defines. -/
syntax (name := book) "book " str : attr

initialize bookAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `book
    descr := "the textbook label of the statement or definition that this \
      declaration states, proves or defines"
    getParam := fun _ stx => match stx with
      | `(attr| book $s:str) => pure s.getString
      | _ => throwError "usage: @[book \"label\"]"
  }

/-- `#book "label"` prints every declaration tied to a textbook label, sorted
by name. -/
elab "#book " s:str : command => do
  let env ← getEnv
  let label := s.getString
  let tied := (env.constants.toList : List (Name × ConstantInfo)).filter
    fun (n, _) => bookAttr.getParam? env n == some label
  let tied := tied.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  if tied.isEmpty then
    logInfo m!"no declaration is tied to {label}"
  for (n, ci) in tied do
    let ty ← liftTermElabM (Meta.ppExpr ci.type)
    logInfo m!"{n} : {ty}"

end Artform
