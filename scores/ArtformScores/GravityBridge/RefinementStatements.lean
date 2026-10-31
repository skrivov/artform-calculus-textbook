import ArtformScores.GravityBridge.RefinementDefs

/-! # Refinement elimination and retained memory -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:refinement-elimination** (refinement elimination and retained memory). -/
@[ledger "GAC:refinement-elimination"]
def refinementLaw : Prop :=
  (∀ h0 h1 c d j : ℚ, h0 ≠ 0 → h1 ≠ 0 → h0 + h1 ≠ 0 →
    refinedAction h0 h1 c d j = reducedAction h0 h1 c j +
      (h0 + h1) / (2 * h0 * h1) * (d - stationaryDetail h0 h1 j) ^ 2) ∧
  (∀ h0 h1 c d j : ℚ, 0 < h0 → 0 < h1 →
    reducedAction h0 h1 c j ≤ refinedAction h0 h1 c d j ∧
    (refinedAction h0 h1 c d j = reducedAction h0 h1 c j ↔
      d = stationaryDetail h0 h1 j)) ∧
  (∀ e : Fin 2 → ℚ,
    edgeDetailEquiv (unequalFineStep e) = coarseDetailStep (edgeDetailEquiv e)) ∧
  (∀ x : ℚ × ℚ, (coarseDetailStep (coarseDetailStep x)).1 =
    (5 / 2 : ℚ) * (coarseDetailStep x).1 - x.1) ∧
  (¬ ∃ U : ℚ → ℚ, ∀ c d, (coarseDetailStep (c, d)).1 = U c)

end Artform.Scores.GravityBridge.Statement
