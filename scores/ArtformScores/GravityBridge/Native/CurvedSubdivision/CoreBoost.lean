import ArtformScores.GravityBridge.Native.Full40.Coordinates

/-! # Supporting original curved subdivision algebra -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision
open Matrix Full40
variable {K : Type*} [Field K] [CharZero K]

def boost (c s : K) : Frame K := !![c, s, 0, 0;s, c, 0, 0;0, 0, 1, 0;0, 0, 0, 1]
def qC (q : K) : K := (q + q⁻¹) / 2
def qS (q : K) : K := (q - q⁻¹) / 2
def internalMetric : Frame K := Matrix.diagonal eta

def rootBoostCurvature (c s : K) : Frame K :=
  (-1 / 2 : K) • (boost c s - boost c (-s))

def inheritedCoframe (h b : K) : Frame K := Matrix.diagonal ![h, 1, b, 1]

lemma rational_boost_guard (q : K) (hq : q ≠ 0) : (qC q) ^ 2 - (qS q) ^ 2 = 1 := by
  unfold qC qS
  field_simp
  ring

omit [CharZero K] in
lemma boost_inverse_and_metric (c s : K) (hc : c ^ 2 - s ^ 2 = 1) :
    boost c s * boost c (-s) = 1 ∧ boost c (-s) * boost c s = 1 ∧
      (boost c s).transpose * internalMetric * boost c s = internalMetric := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i l <;> fin_cases i <;> fin_cases l <;>
    norm_num [boost, internalMetric, eta, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ]
  all_goals first | exact hc | linear_combination hc | linear_combination -hc | ring

omit [CharZero K] in
lemma actual_boost_face_product (c s : K) :
    boost c s * boost c s = boost (c ^ 2 + s ^ 2) (2 * c * s) := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    norm_num [boost, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

lemma actual_inverse_skew_boost (c s : K) :
    rootBoostCurvature c s = lie ![-s, 0, 0, 0, 0, 0] := by
  ext i l
  fin_cases i <;> fin_cases l <;> norm_num [rootBoostCurvature, boost, lie] <;> ring

omit [CharZero K] in
lemma actual_half_chart (h b : K) :
    inheritedCoframe h b * Matrix.diagonal ![1 / 2, 1, 1, 1] = inheritedCoframe (h / 2) b := by
  rw [inheritedCoframe, inheritedCoframe, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp
  ring

lemma actual_child_volume (h b : K) :
    (inheritedCoframe (h / 2) b).det + (inheritedCoframe (h / 2) b).det =
      (inheritedCoframe h b).det := by
  norm_num [inheritedCoframe, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

omit [CharZero K] in
lemma intrinsic_shared_columns (h b : K) (i : Fin 3) (a : Fin 4) :
    inheritedCoframe (h / 2) b a i.succ = inheritedCoframe h b a i.succ := by
  fin_cases i <;> fin_cases a <;> simp [inheritedCoframe]

/-! ## Non-vacuity -/
example : (qC (2 : ℚ), qS (2 : ℚ)) = (5 / 4, 3 / 4) ∧
    (qC (2 : ℚ)) ^ 2 - (qS (2 : ℚ)) ^ 2 = 1 := by
  norm_num [qC, qS]
end Artform.Scores.GravityBridge.Native.CurvedSubdivision
