import ArtformScores.GravityBridge.Native.PreparationDefs

/-! # Exact connection preparation statements -/

namespace Artform.Scores.GravityBridge.Native.Statement

/-- **GAC:connection-preparation** (the eliminated native connection is not a zero register). -/
@[ledger "GAC:connection-preparation"]
def connectionPreparationLaw : Prop :=
  (∀ (z : ℚ) (c : Fin 3 → ℚ),
    connectionEquation z c ↔ c = connectionPreparation z) ∧
  (∀ z : ℚ, connectionEquation z 0 ↔ z = 0) ∧
  christoffelInput 0 1 = 23 / 10 ∧
  christoffelInput 0 2 = -3 / 4 ∧
  christoffelInput 1 2 = -3 / 2 ∧
  (∀ i j : Fin 3, i < j → ¬ connectionEquation (christoffelInput i j) 0) ∧
  (∀ (z : ℚ) (c δ : Fin 3 → ℚ) (ε : ℚ),
    connectionAction z (c + ε • δ) =
      connectionAction z c +
        ε * dotProduct δ (Matrix.mulVec connectionBlock c + (2 * kappa) • connectionSource z) +
        ε ^ 2 / 2 * dotProduct δ (Matrix.mulVec connectionBlock δ)) ∧
  (∀ z : ℚ,
    completeConnectionAction z (connectionPreparation z) = -2 * z ^ 2 / 103 ∧
    connectionAction z (connectionPreparation z) = 4 * z ^ 2 / 10403)

end Artform.Scores.GravityBridge.Native.Statement
