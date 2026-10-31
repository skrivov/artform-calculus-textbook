import ArtformScores.GravityBridge.BoundaryAnchoringDefs
/-! # A component source requires a boundary prescription -/
namespace Artform.Scores.GravityBridge.Statement
open Native
/-- **GAC:boundary-anchoring** (a component source requires a boundary prescription). -/
@[ledger "GAC:boundary-anchoring"]
def boundaryAnchoringLaw : Prop :=
  (∀ (a b j : ℚ),
    freeTwoCellBoundary a b j ↔ a = b ∧ j = 0) ∧
  (∀ (rho a b j : ℚ) (_hr : rho ≠ 0),
    anchoredTwoCellAction rho a b j = anchoredTwoCellMinimum rho j +
      rho * ((a + b) / 2 - j / (2 * rho)) ^ 2 +
      (kappa / 2 + rho / 4) * (b - a) ^ 2) ∧
  (∀ (rho a b j : ℚ) (_hr : 0 < rho),
    anchoredTwoCellMinimum rho j ≤ anchoredTwoCellAction rho a b j ∧
    (anchoredTwoCellAction rho a b j = anchoredTwoCellMinimum rho j ↔
      a = j / (2 * rho) ∧ b = j / (2 * rho)))
end Artform.Scores.GravityBridge.Statement
