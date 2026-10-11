import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Basic
import ArtformTextbook.Meta.Book

/-!
# Rods (Sections 1.2, 1.3 and 1.11)

Section 1.11 builds the rods by two rules, `rod` and `glue`, and by no others,
and defines their cells and their order by the elimination rule. This file
writes those rules in Lean, and Definition 1.2 (perfect alignment).
-/

namespace Artform

/-- The two tags of an ordered gluing (Section 1.2): `L` for the left part,
`R` for the right. -/
inductive Tag where
  | L
  | R
  deriving DecidableEq

/-- The rods of Section 1.11, built by the rules `rod` and `glue` and by no
others. -/
inductive OrderedForm where
  /-- `R_n`: `n` cells in a row. -/
  | rod : ℕ → OrderedForm
  /-- `glue(P, Q)`: the cells of `P` before those of `Q`, the seam kept. -/
  | glue : OrderedForm → OrderedForm → OrderedForm

namespace OrderedForm

/-- The cells of a rod, by the computation rules of Section 1.11:
`cells(R_n) = {0, …, n-1}`, and `cells(glue(P,Q))` is the tagged choice
`Σ (t : {L, R}), cells(F t)` with `F L = P` and `F R = Q`. -/
@[reducible] def cells : OrderedForm → Type
  | rod n => Fin n
  | glue P Q => (t : Tag) × (match t with
      | .L => P.cells
      | .R => Q.cells)

/-- The order on the cells of a rod (Section 1.11). In `R_n` the cell `i`
comes before `j` when `i < j`; in `glue(P,Q)` every `(L,p)` comes before every
`(R,q)`, and two cells with one tag come in the order of `P` or of `Q`. -/
def before : (X : OrderedForm) → X.cells → X.cells → Prop
  | rod _, i, j => i < j
  | glue P _, ⟨.L, p⟩, ⟨.L, p'⟩ => P.before p p'
  | glue _ _, ⟨.L, _⟩, ⟨.R, _⟩ => True
  | glue _ _, ⟨.R, _⟩, ⟨.L, _⟩ => False
  | glue _ Q, ⟨.R, q⟩, ⟨.R, q'⟩ => Q.before q q'

end OrderedForm

/-- **Definition 1.2** (perfect alignment). A perfect alignment of two finite
rods is an order-preserving bijection between their cells. Here a rod is given
by its type of cells with a linear order; order-preserving is read as
monotone, which for a bijection between linear orders is the same as strictly
monotone. -/
@[book "nolabel:01-foundations:perfect-alignment"]
def Align (P Q : Type*) [LinearOrder P] [LinearOrder Q] : Type _ :=
  { α : P → Q // Function.Bijective α ∧ Monotone α }

end Artform
