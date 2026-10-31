import ArtformScores.GravityBridge.Native.Retrospective.TTForceDefs
/-! # The original lower temporal forcing through repeated-factor cancellation -/
namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement
open Matrix
/-- **GAC2:temporal-forcing-factor-cancellation**
(the original lower temporal forcing through repeated-factor cancellation). -/
@[ledger "GAC2:temporal-forcing-factor-cancellation"]
def tTForceLaw : Prop :=
    (∀ (t R L : ℚ) (_ht : t ≠ 0) (_hR : R ≠ 0)
    (_ha : 1 + 2 * t ≠ 0) (_hb : 1 - t ≠ 0),
    -temporalForceCoefficient t R L / temporalPrincipalCoefficient t R = -t * R * L / 2) ∧
    (repeatedH kappa = 10201 / 10300) ∧
    (temporalForceCoefficient kappa (rhoSquared momentum)
      (diagonalContraction momentum polarization) = -63 / 12875 ∧
    -temporalForceCoefficient kappa (rhoSquared momentum)
      (diagonalContraction momentum polarization) /
      temporalPrincipalCoefficient kappa (rhoSquared momentum) = 36 / 505) ∧
    (-temporalForceCoefficient kappa (rhoSquared momentum)
      (diagonalContraction momentum polarization) /
      temporalPrincipalCoefficient kappa (rhoSquared momentum) =
      temporalSymbol momentum polarization)
end Artform.Scores.GravityBridge.Native.Retrospective.Statement
