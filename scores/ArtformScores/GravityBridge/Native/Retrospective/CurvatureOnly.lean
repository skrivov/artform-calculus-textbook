import ArtformScores.GravityBridge.Native.Retrospective.CurvatureOnlyStatements

/-! # Curvature-only elimination fails the original signed force -/

namespace Artform.Scores.GravityBridge.Native.Retrospective

open Matrix



open Matrix

lemma curvature_source_eigen (z : ℚ) :
    curvatureBlock *ᵥ connectionSource z = -connectionSource z := by
  ext i
  fin_cases i <;> simp [curvatureBlock, connectionSource, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
lemma parameter_source_eigen (t z : ℚ) :
    paramConnection t *ᵥ connectionSource z = -(1 + 2 * t) • connectionSource z := by
  rw [parameter_block_factor]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, curvature_source_eigen]
  module
lemma curvature_only_equation (t z : ℚ) :
    curvatureBlock *ᵥ curvatureOnlyPreparation t z + (2 * t) • connectionSource z = 0 := by
  rw [curvatureOnlyPreparation, Matrix.mulVec_smul, curvature_source_eigen]
  module
lemma curvature_only_full_residual (t z : ℚ) :
    paramConnection t *ᵥ curvatureOnlyPreparation t z + (2 * t) • connectionSource z =
      (-4 * t ^ 2) • connectionSource z := by
  rw [curvatureOnlyPreparation, Matrix.mulVec_smul, parameter_source_eigen]
  module
lemma spectral_preparation_equation (t z : ℚ) (hm : 1 + 2 * t ≠ 0) :
    paramConnection t *ᵥ spectralPreparation t z + (2 * t) • connectionSource z = 0 := by
  rw [spectralPreparation, Matrix.mulVec_smul, parameter_source_eigen, smul_smul]
  have he : (2 * t / (1 + 2 * t)) * -(1 + 2 * t) = -2 * t := by field_simp
  rw [he]
  module
lemma native_spectral_preparation (z : ℚ) :
    spectralPreparation kappa z = connectionPreparation z := by
  ext i
  fin_cases i <;> norm_num [spectralPreparation, kappa, connectionSource,
    connectionPreparation] <;> ring
lemma native_curvature_only_iff (z : ℚ) :
    connectionEquation z (curvatureOnlyPreparation kappa z) ↔ z = 0 := by
  rw [connectionEquation, ← native_parameter_block, curvature_only_full_residual]
  constructor
  · intro h
    have he := congrFun h 2
    norm_num [kappa, connectionSource] at he
    exact he
  · rintro rfl
    simp [connectionSource]
lemma action_identification (z : ℚ) (c : Fin 3 → ℚ) :
    paramCompleteAction kappa z c = completeConnectionAction z c := by
  unfold paramCompleteAction completeConnectionAction connectionAction
  rw [native_parameter_block]
  abel
lemma spectral_effective_action (t z : ℚ) (hm : 1 + 2 * t ≠ 0) :
    paramCompleteAction t z (spectralPreparation t z) = -2 * t * z ^ 2 / (1 + 2 * t) := by
  have he := spectral_preparation_equation t z hm
  have hr : paramConnection t *ᵥ spectralPreparation t z = -(2 * t) • connectionSource z := by
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left he
  rw [paramCompleteAction, hr]
  simp [spectralPreparation, connectionSource, dotProduct, Fin.sum_univ_succ]
  field_simp
  ring
lemma curvature_only_action_error (t z : ℚ) (hm : 1 + 2 * t ≠ 0) :
    paramCompleteAction t z (curvatureOnlyPreparation t z) -
      paramCompleteAction t z (spectralPreparation t z) =
        -16 * t ^ 4 * z ^ 2 / (1 + 2 * t) := by
  rw [spectral_effective_action t z hm]
  unfold paramCompleteAction curvatureOnlyPreparation
  rw [Matrix.mulVec_smul, parameter_source_eigen]
  simp [connectionSource, dotProduct, Fin.sum_univ_succ]
  field_simp
  ring

/-- **GAC2:curvature-only-force-residual**
(curvature-only elimination fails the original signed force). -/
@[ledger "GAC2:curvature-only-force-residual"]
theorem curvatureOnlyLaw : Statement.curvatureOnlyLaw := by
  exact ⟨curvature_source_eigen,
    parameter_source_eigen,
    curvature_only_equation,
    curvature_only_full_residual,
    spectral_preparation_equation,
    native_spectral_preparation,
    native_curvature_only_iff,
    action_identification,
    spectral_effective_action,
    curvature_only_action_error⟩

/-! ## Non-vacuity: curvature-only preparation fails the original native block -/
example : ¬ connectionEquation 1 (curvatureOnlyPreparation kappa 1) := by
  rw [native_curvature_only_iff]
  norm_num

end Artform.Scores.GravityBridge.Native.Retrospective
