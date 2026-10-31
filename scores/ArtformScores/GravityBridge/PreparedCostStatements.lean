import ArtformScores.GravityBridge.PreparedCostDefs

/-! # Prepared connection coefficient cost and reset test -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:prepared-connection-cost** (prepared connection coefficient cost and reset test). -/
@[ledger "GAC:prepared-connection-cost"]
def preparedCostLaw : Prop :=
  (∀ z : ℚ, oddConnectionMatch z (Native.connectionPreparation z)) ∧
  (∀ (z : ℚ) (c : Fin 3 → ℚ), Native.connectionEquation z c → oddConnectionMatch z c) ∧
  (∀ (z : ℚ) (c : Fin 3 → ℚ), oddConnectionMatch z c →
    connectionCoefficientCost c = 8 * z ^ 2 / 10609 + c 0 ^ 2 + (c 1 + c 2) ^ 2 / 2) ∧
  (∀ (z : ℚ) (c : Fin 3 → ℚ), oddConnectionMatch z c →
    8 * z ^ 2 / 10609 ≤ connectionCoefficientCost c ∧
    (connectionCoefficientCost c = 8 * z ^ 2 / 10609 ↔
      c = Native.connectionPreparation z)) ∧
  (∀ z : ℚ, z ≠ 0 →
    ((z, Native.connectionPreparation z) : ℚ × (Fin 3 → ℚ)).1 = (z, 0).1 ∧
    (Native.connectionPreparation z 1 - Native.connectionPreparation z 2) ≠ (0 : ℚ) ∧
    ¬ Native.connectionEquation z 0)

end Artform.Scores.GravityBridge.Statement
