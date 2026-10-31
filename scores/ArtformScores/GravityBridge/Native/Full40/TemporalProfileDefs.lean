import ArtformScores.GravityBridge.Native.Full40.Projector
/-! # Higher temporal Lorentz jets with explicit real profile bounds -/
namespace Artform.Scores.GravityBridge.Native.Full40
noncomputable def temporalGaugeProfile (h c t : ℝ) : ℝ := c * (t / h) ^ 2
noncomputable def boundedTemporalProfile (h c t : ℝ) : ℝ :=
  c * ((1 + h ^ 2) / h ^ 2) * (t ^ 2 / (1 + t ^ 2))
end Artform.Scores.GravityBridge.Native.Full40
