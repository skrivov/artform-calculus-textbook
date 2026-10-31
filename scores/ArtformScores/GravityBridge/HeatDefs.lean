import ArtformScores.GravityBridge.GaussianDefs

/-! # The normalized real Gaussian boundary kernel -/

namespace Artform.Scores.GravityBridge

noncomputable section

def heatKernel (h x y : ℝ) : ℝ := (Real.sqrt (2 * Real.pi * h))⁻¹ *
  Real.exp (-(y - x) ^ 2 / (2 * h))

end

end Artform.Scores.GravityBridge
