import ArtformScores.GravityBridge.TwoCell
/-! # A component source requires a boundary prescription -/
namespace Artform.Scores.GravityBridge
noncomputable section
open Native
def freeTwoCellBoundary (a b j : ℚ) : Prop :=
  kappa * (b - a) + j / 2 = 0 ∧ kappa * (b - a) - j / 2 = 0
def anchoredTwoCellAction (rho a b j : ℚ) : ℚ :=
  twoCellEffective a b j + rho / 2 * (a ^ 2 + b ^ 2)
def anchoredTwoCellMinimum (rho j : ℚ) : ℚ := -j ^ 2 / (4 * rho) - j ^ 2 / (8 * kappa)
end
end Artform.Scores.GravityBridge
