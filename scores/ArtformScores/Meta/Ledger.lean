import Lean

/-!
# Ties to the research ledger

`@[ledger "label"]` ties a declaration to a statement of the algebra of scores,
by its label there (`R1` … `R6`, `T1` … `T16`):

* on a `def … : Prop` in `Artform.Scores.Statement`, it marks the Lean form of
  the statement, which an independent review checks against the ledger;
* on a `theorem`, it marks the proof of that statement;
* on any other declaration, it marks the Lean form of a ledger definition.

`#ledger "label"` lists the declarations tied to a label.
`scripts/LedgerReport.lean` lists all of them, and `scripts/ledger_status.py`
checks that each proof proves exactly the statement with its label.
-/

namespace Artform.Scores
open Lean Elab Command

/-- `@[ledger "label"]`: the ledger label of the statement or definition that
this declaration states, proves or defines. -/
syntax (name := ledger) "ledger " str : attr

initialize ledgerAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `ledger
    descr := "the ledger label of the statement or definition that this \
      declaration states, proves or defines"
    getParam := fun _ stx => match stx with
      | `(attr| ledger $s:str) => pure s.getString
      | _ => throwError "usage: @[ledger \"label\"]"
  }

/-- `#ledger "label"` prints every declaration tied to a ledger label, sorted
by name. -/
elab "#ledger " s:str : command => do
  let env ← getEnv
  let label := s.getString
  let tied := (env.constants.toList : List (Name × ConstantInfo)).filter
    fun (n, _) => ledgerAttr.getParam? env n == some label
  let tied := tied.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  if tied.isEmpty then
    logInfo m!"no declaration is tied to {label}"
  for (n, ci) in tied do
    let ty ← liftTermElabM (Meta.ppExpr ci.type)
    logInfo m!"{n} : {ty}"

end Artform.Scores
