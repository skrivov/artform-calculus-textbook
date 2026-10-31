import ArtformScores.GravityBridge.Native.TemporalWitness
/-! # The original lower temporal forcing through repeated-factor cancellation -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
open Matrix
def repeatedH (t : ℚ) : ℚ := ((1 + 2 * t) * (1 - t))⁻¹
def temporalForceCoefficient (t R L : ℚ) : ℚ :=
  t ^ 2 * R ^ 2 * L / (4 * (1 + 2 * t) * (1 - t))
def temporalPrincipalCoefficient (t R : ℚ) : ℚ := t * R * repeatedH t / 2
end Artform.Scores.GravityBridge.Native.Retrospective
