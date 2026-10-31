import ArtformScores.GravityBridge.HeatDefs

/-! # Normalized Gaussian gluing and a discarded-detail test -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:normalized-gaussian-gluing** (normalized gaussian gluing and a discarded-detail test). -/
@[ledger "GAC:normalized-gaussian-gluing"]
def heatLaw : Prop :=
  (∀ h0 h1 : ℝ, 0 < h0 → 0 < h1 →
    (Real.sqrt (2 * Real.pi * h0))⁻¹ * (Real.sqrt (2 * Real.pi * h1))⁻¹ *
      Real.sqrt (Real.pi / ((h0 + h1) / (2 * h0 * h1))) =
        (Real.sqrt (2 * Real.pi * (h0 + h1)))⁻¹) ∧
  (∀ h0 h1 x y : ℝ, 0 < h0 → 0 < h1 →
    MeasureTheory.Integrable (fun m : ℝ => heatKernel h0 x m * heatKernel h1 m y) ∧
    (∫ m : ℝ, heatKernel h0 x m * heatKernel h1 m y) = heatKernel (h0 + h1) x y) ∧
  (let h : ℝ := 1 / (2 * Real.pi);
    heatKernel h 0 0 * heatKernel h 0 0 = 1 ∧
      heatKernel (h + h) 0 0 = (Real.sqrt 2)⁻¹ ∧
      heatKernel h 0 0 * heatKernel h 0 0 ≠ heatKernel (h + h) 0 0)

end Artform.Scores.GravityBridge.Statement
