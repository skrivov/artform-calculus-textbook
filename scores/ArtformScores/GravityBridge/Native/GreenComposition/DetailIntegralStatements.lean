import ArtformScores.GravityBridge.Native.GreenComposition.DetailIntegralDefs

/-! # Integrate the same source-bearing detail with its measure -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition.Statement

open scoped BigOperators
open MeasureTheory

/-- **GAC2:two-cell-source-detail-measure**
(integrate the same source-bearing detail with its measure). -/
@[ledger "GAC2:two-cell-source-detail-measure"]
def detailIntegralLaw : Prop :=
    (∀ (c a b j : ℝ) (_hc : 0 < c),
    Integrable (fun m : ℝ => Real.exp (-sourceAction c a m b j)) ∧
    (∫ m : ℝ, Real.exp (-sourceAction c a m b j)) =
      Real.exp (-sourceEffective c a b j) * Real.sqrt (Real.pi / (2 * c))) ∧
    (∀ (c a b j : ℝ) (_hc : 0 < c)
    (_hn : Real.sqrt (Real.pi / (2 * c)) ≠ 1),
    (∫ m : ℝ, Real.exp (-sourceAction c a m b j)) ≠ Real.exp (-sourceEffective c a b j)) ∧
    (Real.sqrt (Real.pi / (2 * (1 / 101 : ℝ))) ≠ 1) ∧
    (∀ (f : ℝ → ℝ),
    (∫ z : ℝ, f (2 * z)) = (1 / 2 : ℝ) * (∫ m : ℝ, f m))

end Artform.Scores.GravityBridge.Native.GreenComposition.Statement
