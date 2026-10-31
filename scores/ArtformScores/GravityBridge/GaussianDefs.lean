import ArtformScores.GravityBridge.LinearDefs

/-! # A real convergent Gaussian Schur problem with sources -/

namespace Artform.Scores.GravityBridge

noncomputable section

def gaussianAction (a b c j k q z : ℝ) : ℝ :=
  a * z ^ 2 + 2 * b * q * z + c * q ^ 2 - 2 * j * z - 2 * k * q

def gaussianEffective (a b c j k q : ℝ) : ℝ :=
  (c - b ^ 2 / a) * q ^ 2 - 2 * (k - b * j / a) * q - j ^ 2 / a

def gaussianCenter (a b j q : ℝ) : ℝ := (j - b * q) / a

end

end Artform.Scores.GravityBridge
