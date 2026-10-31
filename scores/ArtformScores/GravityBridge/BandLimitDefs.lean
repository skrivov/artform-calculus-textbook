import ArtformScores.GravityBridge.LinearDefs

/-! # A fixed compact frequency space and its Gaussian multiplier operator -/

namespace Artform.Scores.GravityBridge

noncomputable section

abbrev FrequencyBand (R : ℝ) := Set.Icc (-R) R

def gaussianMultiplier (h R : ℝ) : C(FrequencyBand R, ℝ) where
  toFun x := Real.exp (-h * (x : ℝ) ^ 2 / 2)
  continuous_toFun := by fun_prop

def gaussianBandStep (h R : ℝ) :
    C(FrequencyBand R, ℝ) →L[ℝ] C(FrequencyBand R, ℝ) :=
  ContinuousLinearMap.mul ℝ _ (gaussianMultiplier h R)

end

end Artform.Scores.GravityBridge
