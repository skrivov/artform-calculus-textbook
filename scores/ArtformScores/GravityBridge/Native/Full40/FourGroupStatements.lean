import ArtformScores.GravityBridge.Native.Full40.FourGroupDefs
/-! # The guarded complete four-group longitudinal target -/
namespace Artform.Scores.GravityBridge.Native.Full40.Statement
/-- **GAC2:guarded-four-group-target**
(the guarded complete four-group longitudinal target). -/
@[ledger "GAC2:guarded-four-group-target"]
def fourGroupLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (j rho d4 : K) (_hj : j ≠ 0) (_hr : rho ≠ 0) (_hd : d4 ≠ 0)
    (groups : Fin 4 → K),
    normalizedTarget j rho d4 groups = 0 ↔ fourGroupValue groups = 0) ∧
    (∀ (j rho d4 : K) (_hj : j ≠ 0) (_hr : rho ≠ 0) (_hd : d4 ≠ 0)
    (n : Fin 3 → K) (_hn : ∃ a, n a ≠ 0) (groups : Fin 4 → K),
    temporalBoostContact n (normalizedTarget j rho d4 groups) = 0 ↔ fourGroupValue groups = 0) ∧
    (∀ (groups : Fin 4 → K),
    fourGroupValue groups =
    groups 0 + groups 1 + groups 2 + groups 3) ∧
    (fourGroupValue (![1, -1, 0, 0] : Fin 4 → ℚ) = 0 ∧
      (![1, -1, 0, 0] : Fin 4 → ℚ) 0 ≠ 0) ∧
    (HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 ∧
    HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 ∧ (1 : ℝ) ≠ 0)
end Artform.Scores.GravityBridge.Native.Full40.Statement
