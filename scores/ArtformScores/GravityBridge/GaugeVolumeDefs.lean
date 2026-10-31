import ArtformScores.GravityBridge.Gaussian

/-! # A singular Gaussian and its explicit regulator -/

namespace Artform.Scores.GravityBridge

noncomputable section

def gaugeGaussian (epsilon : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.exp (-(x.1 ^ 2 + epsilon * x.2 ^ 2))

end

end Artform.Scores.GravityBridge
