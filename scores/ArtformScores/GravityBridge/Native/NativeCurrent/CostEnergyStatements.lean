import ArtformScores.GravityBridge.Native.NativeCurrent.CostEnergyDefs

/-! # Exact coefficient work does not fund quadratic energy -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent.Statement

open Matrix TTCoordinates

/-- **GAC2:declared-cost-quadratic-energy**
(exact coefficient work does not fund quadratic energy). -/
@[ledger "GAC2:declared-cost-quadratic-energy"]
def costEnergyLaw : Prop :=
    (∀ (a : ℚ),
    originalLeadingEnergy 14 (a • polarization) 0 = 7 * a ^ 2 / 2) ∧
    (∀ (a : ℚ),
    ttScales contractedForcingProgram = 1 ∧ ttAdds contractedForcingProgram = 0 ∧
    evalTTExpr (a • polarization) contractedForcingProgram = (36 / 505 : ℚ) * a) ∧
    (∀ (M : ℚ),
    ∃ a : ℚ, ttScales contractedForcingProgram = 1 ∧
      M < originalLeadingEnergy 14 (a • polarization) 0)

end Artform.Scores.GravityBridge.Native.NativeCurrent.Statement
