import ArtformScores.GravityBridge.Native.R8Domains
/-! # Joint angular spacing and nonlinear budget audit -/
namespace Artform.Scores.GravityBridge
noncomputable section
open Native.R8
def cancellingAnnularRemainder (h : ℝ) : ℝ := -h ^ 4 * leadingScalar (approachingRay h)
end
end Artform.Scores.GravityBridge
