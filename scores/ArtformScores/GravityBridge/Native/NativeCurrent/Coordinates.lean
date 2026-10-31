import ArtformScores.GravityBridge.Native.NativeCurrent.CoordinatesStatements

/-! # Original metric momentum and velocity current factors -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent

open Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

open Matrix
lemma tensor_dot_smul_left (x y : Matrix (Fin 3) (Fin 3) ℚ) (a : ℚ) :
    tensorDot (a • x) y = a * tensorDot x y := by
  simp [tensorDot, Finset.mul_sum, mul_assoc]

lemma tensor_dot_smul_right (x y : Matrix (Fin 3) (Fin 3) ℚ) (a : ℚ) :
    tensorDot x (a • y) = a * tensorDot x y := by
  simp [tensorDot, Finset.mul_sum, mul_left_comm]

lemma original_coframe_metric_factor (q p r s : Matrix (Fin 3) (Fin 3) ℚ) :
    coframeCut ((1 / 2 : ℚ) • q) p ((1 / 2 : ℚ) • r) s = metricMomentumCut q p r s := by
  rw [coframeCut, tensor_dot_smul_left, tensor_dot_smul_left, metricMomentumCut]
  ring

lemma original_metric_velocity_factor (q p r s : Matrix (Fin 3) (Fin 3) ℚ) :
    metricVelocityCut q ((2 : ℚ) • p) r ((2 : ℚ) • s) = metricMomentumCut q p r s := by
  rw [metricVelocityCut, tensor_dot_smul_right, tensor_dot_smul_right, metricMomentumCut]
  ring

lemma physical_connection_current_pullback (B : V →ₗ[K] V →ₗ[K] K)
    (f c g d : V) (h : K) :
    B (f - h • c) (g - h • d) = B f g - h * B f d - h * B c g + h ^ 2 * B c d := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

lemma original_unit_dyad_pair :
    metricMomentumCut polarization 0 0 polarization = -1 ∧
    metricVelocityCut polarization 0 0 ((2 : ℚ) • polarization) = -1 := by
  constructor
  · norm_num [metricMomentumCut, tensorDot, polarization, Fin.sum_univ_succ]
  · norm_num [metricVelocityCut, tensorDot, polarization, Fin.sum_univ_succ]

/-- **GAC2:native-current-coordinate-factors**
(original metric momentum and velocity current factors). -/
@[ledger "GAC2:native-current-coordinate-factors"]
theorem coordinatesLaw : Statement.coordinatesLaw := by
  intro K V _ _ _
  exact ⟨tensor_dot_smul_left,
    tensor_dot_smul_right,
    original_coframe_metric_factor,
    original_metric_velocity_factor,
    physical_connection_current_pullback,
    original_unit_dyad_pair⟩

/-! ## Non-vacuity -/

example : metricMomentumCut polarization 0 0 polarization ≠ 0 := by
  rw [original_unit_dyad_pair.1]
  norm_num

end Artform.Scores.GravityBridge.Native.NativeCurrent
