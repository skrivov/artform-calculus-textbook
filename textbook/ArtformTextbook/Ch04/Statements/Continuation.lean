import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ArtformTextbook.Ch04.Defs.Continuation

/-!
# Statements of Chapter 4: one continuing experiment (Section 4.10)

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

open MeasureTheory
open scoped NNReal

/-- **Proposition 4.5** (extension of compatible finite histories). Suppose
normalized nonnegative laws `P_n` on the first `n` report alphabets satisfy
`∑_{y ∈ Y_{n+1}} P_{n+1}(h, y) = P_n(h)`. There is exactly one probability
measure on `(Ω_∞, 𝒜_∞)` assigning mass `P_n(h)` to `[h]`.

The finite nonempty alphabets `Y_1, Y_2, …` of the book are `Y 0, Y 1, …`, so a
word `h : (i : Fin n) → Y i` is a prefix over the first `n` alphabets, and
`(h, y)` is `Fin.snoc h y`. The law `P n` gives each such word a nonnegative
real mass, and is normalized when its masses add up to `1`. The book's laws
start at `n = 1`, so `P 0` is not used. -/
@[book "probbook:history-extension"]
def historyExtension : Prop :=
  ∀ (Y : ℕ → Type) [∀ t, Fintype (Y t)] [∀ t, Nonempty (Y t)]
    (P : (n : ℕ) → ((i : Fin n) → Y i) → ℝ≥0),
    (∀ n, 1 ≤ n → ∑ h, P n h = 1) →
    (∀ n, 1 ≤ n → ∀ h : (i : Fin n) → Y i, ∑ y : Y n, P (n + 1) (Fin.snoc h y) = P n h) →
    letI := cylinderAlgebra Y
    ∃! μ : Measure ((t : ℕ) → Y t), IsProbabilityMeasure μ ∧
      ∀ n, 1 ≤ n → ∀ h : (i : Fin n) → Y i, μ (prefixCylinder h) = P n h

end Artform.Statement
