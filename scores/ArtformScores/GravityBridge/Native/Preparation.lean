import ArtformScores.GravityBridge.Native.PreparationStatements
import ArtformScores.GravityBridge.Native.DistinctBlock

/-! # A native Schur cancellation does not permit a zero connection preparation -/

namespace Artform.Scores.GravityBridge.Native

open Matrix

theorem prepared_connection (z : ℚ) : connectionEquation z (connectionPreparation z) := by
  unfold connectionEquation
  ext i
  fin_cases i <;>
    norm_num [connectionPreparation, connectionSource, connectionBlock, curvatureBlock,
      kappa, torsionBlock, facePairing, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

theorem connectionEquation_iff (z : ℚ) (c : Fin 3 → ℚ) :
    connectionEquation z c ↔ c = connectionPreparation z := by
  constructor
  · intro h
    apply Matrix.mulVec_injective_of_det_ne_zero connectionBlock_det_ne_zero
    exact add_right_cancel (h.trans (prepared_connection z).symm)
  · rintro rfl
    exact prepared_connection z

theorem zero_connection_iff (z : ℚ) : connectionEquation z 0 ↔ z = 0 := by
  constructor
  · intro h
    have hi := congrFun h (1 : Fin 3)
    norm_num [connectionSource, kappa] at hi
    linarith
  · rintro rfl
    unfold connectionEquation
    ext i
    fin_cases i <;> norm_num [connectionSource, kappa]

theorem connectionAction_variation (z : ℚ) (c δ : Fin 3 → ℚ) (ε : ℚ) :
    connectionAction z (c + ε • δ) =
      connectionAction z c +
        ε * dotProduct δ (connectionBlock *ᵥ c + (2 * kappa) • connectionSource z) +
        ε ^ 2 / 2 * dotProduct δ (connectionBlock *ᵥ δ) := by
  norm_num [connectionAction, connectionBlock, curvatureBlock, kappa, torsionBlock,
    facePairing, connectionSource, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.one_apply, Fin.sum_univ_succ]
  ring

theorem connectionAction_prepared (z : ℚ) :
    connectionAction z (connectionPreparation z) = 4 * z ^ 2 / 10403 := by
  norm_num [connectionAction, connectionPreparation, connectionBlock, curvatureBlock,
    kappa, torsionBlock, facePairing, connectionSource, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.sum_univ_succ]
  ring

theorem completeConnectionAction_prepared (z : ℚ) :
    completeConnectionAction z (connectionPreparation z) = -2 * z ^ 2 / 103 := by
  rw [completeConnectionAction, connectionAction_prepared]
  norm_num [kappa]
  ring

/-- **GAC:connection-preparation** (the eliminated native connection is not a zero register). -/
@[ledger "GAC:connection-preparation"]
theorem connectionPreparationLaw : Statement.connectionPreparationLaw := by
  refine ⟨connectionEquation_iff, zero_connection_iff, ?_, ?_, ?_, ?_,
    connectionAction_variation, fun z =>
      ⟨completeConnectionAction_prepared z, connectionAction_prepared z⟩⟩
  · norm_num [christoffelInput, rhoSquared, momentum, polarization, Fin.sum_univ_succ]
  · norm_num [christoffelInput, rhoSquared, momentum, polarization, Fin.sum_univ_succ]
  · norm_num [christoffelInput, rhoSquared, momentum, polarization, Fin.sum_univ_succ]
  · intro i j hij
    rw [zero_connection_iff]
    fin_cases i <;> fin_cases j <;>
      simp_all [christoffelInput, rhoSquared, momentum, polarization, Fin.sum_univ_succ] <;>
      norm_num

/-! ## Non-vacuity -/

/-- An actual nonzero input from the rational TT test has a unique nonzero
prepared connection, despite its vanishing spatial-face Schur output. -/
example :
    connectionEquation (23 / 10) (connectionPreparation (23 / 10)) ∧
    connectionPreparation (23 / 10) ≠ 0 ∧
    schurCovector (23 / 10) 2 = 0 := by
  refine ⟨prepared_connection _, ?_, ?_⟩
  · intro h
    have hi := congrFun h (1 : Fin 3)
    norm_num [connectionPreparation] at hi
  · rw [schurCovector_eq]
    norm_num

/-- The omitted term changes the input-dependent effective action even though
it leaves the stationary connection equation unchanged. -/
example :
    completeConnectionAction 1 (connectionPreparation 1) ≠
      connectionAction 1 (connectionPreparation 1) := by
  rw [completeConnectionAction_prepared, connectionAction_prepared]
  norm_num

end Artform.Scores.GravityBridge.Native
