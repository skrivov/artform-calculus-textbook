import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ArtformTextbook.Meta.Book

/-!
# The statements of Chapter 4

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition. Measures are Mathlib's (Definitions 3.34 to 3.36
of the book are Mathlib's σ-algebras, measures and measurable maps).
-/

namespace Artform.Statement

open MeasureTheory
open scoped ENNReal

/-- **Proposition 4.2** (counting retained alternatives). For a finite
nonempty set `Ω` of equal-weight retained alternatives, a finite set `Y`, and a
report map `f : Ω → Y`, normalized counting pushes forward to
`P_Y(C) = |f⁻¹(C)| / |Ω|`, `C ⊆ Y`. This is a probability measure on the finite
power set of `Y`. Both sets carry the σ-algebra of all their subsets. -/
@[book "probbook:count-law"]
def countLaw : Prop :=
  ∀ (Ω Y : Type) [Fintype Ω] [Nonempty Ω] [Fintype Y] (f : Ω → Y),
    letI : MeasurableSpace Ω := ⊤
    letI : MeasurableSpace Y := ⊤
    let P : Measure Y := Measure.map f ((Fintype.card Ω : ℝ≥0∞)⁻¹ • Measure.count)
    IsProbabilityMeasure P ∧
      ∀ C : Set Y, P C = (Nat.card (f ⁻¹' C) : ℝ≥0∞) / (Fintype.card Ω : ℝ≥0∞)

end Artform.Statement
