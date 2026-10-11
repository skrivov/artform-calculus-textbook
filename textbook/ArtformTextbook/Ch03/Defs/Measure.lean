import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Basic.NNReal.Defs
import ArtformTextbook.Ch03.Defs.Cube

/-!
# Weighted cellular content (Section 3.9)

Sigma-algebras, measures and measurable maps (Definitions 3.34, 3.35, 3.36 and 3.38) are
Mathlib's `MeasurableSpace`, `MeasureTheory.Measure` and `Measurable`. The book's own definition
in Part D is the weighted cellular content, which weighs the cells of one dimension of a region.
-/

namespace Artform

open scoped NNReal

/-- **Definition 3.41** (weighted cellular content). Fix a dimension `d` and a weight `w_T ≥ 0`
for each allowed `d`-cell type `T`. For a finite cellular region `X`,
`Cont_d(X) = Σ_{c ∈ X_d} w_{type(c)}`, where `X_d` is the set of its `d`-cell identities. Here
the region is a finite set `X` of cells of a canvas `K`, each cell has a type, and the weights
are nonnegative reals. -/
@[book "def:weighted-cellular-content"]
def cellularContent (K : IncidenceCanvas) {T : Type} (type : K.Cell → T) (w : T → ℝ≥0) (d : ℕ)
    (X : Finset K.Cell) : ℝ≥0 :=
  ∑ c ∈ X.filter (fun c => K.dim c = d), w (type c)

end Artform
