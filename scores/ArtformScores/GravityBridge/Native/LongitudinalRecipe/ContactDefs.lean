import ArtformScores.GravityBridge.Native.LongitudinalRecipe.Value
import ArtformScores.GravityBridge.Native.MetricCut.Quartic

/-! # A quantitative temporal-contact test for the supplied fixed recipe -/

namespace Artform.Scores.GravityBridge.Native.LongitudinalRecipe

open Matrix
open MetricCut



noncomputable def referenceQuartic : ℚ := -(38 / 7 : ℚ) * quarticConstant

noncomputable def referenceBoostCoefficient : ℂ :=
  -(total : ℚ) / (56 * Complex.I * (referenceQuartic : ℂ))

end Artform.Scores.GravityBridge.Native.LongitudinalRecipe
