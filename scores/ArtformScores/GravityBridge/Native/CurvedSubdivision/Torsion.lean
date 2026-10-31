import ArtformScores.GravityBridge.Native.CurvedSubdivision.TorsionStatements

/-! # Full ordered nonlinear torsion on the inherited coframe -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40
omit [CharZero K] in
lemma original_torsion_all_components (h b c s : K) :
    exactTorsion h b c s = fun i l =>
      if i = 0 ∧ l = 1 then h • ![1 - c, s, 0, 0] else
        if i = 1 ∧ l = 0 then -(h • ![1 - c, s, 0, 0]) else 0 := by
  ext i l a
  fin_cases i <;> fin_cases l <;> fin_cases a <;>
    norm_num [exactTorsion, inverseLinks, inheritedCoframe, boost,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
        Matrix.diagonal] <;> ring

omit [CharZero K] in
lemma original_coframe_metric_inverse (h b : K) (hh : h ≠ 0) (hb : b ≠ 0) :
    ((inheritedCoframe h b).transpose * internalMetric * inheritedCoframe h b) *
      exactMetricInverse h b = 1 := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    norm_num [inheritedCoframe, internalMetric, exactMetricInverse, eta, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ] <;> field_simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Retain every ordered torsion index and both inverse metric factors before reduction.
lemma original_complete_torsion_density (h b c s : K) (hh : h ≠ 0) (_hb : b ≠ 0)
    (hc : c ^ 2 - s ^ 2 = 1) : exactTorsionDensity h b c s = -2 * h * b * (c - 1) := by
  unfold exactTorsionDensity
  rw [original_torsion_all_components]
  norm_num [inheritedCoframe, Matrix.det_diagonal, Fin.prod_univ_succ, exactMetricInverse,
    etaPair, eta, Fin.sum_univ_succ]
  field_simp
  linear_combination (2 : K) * hc

/-- **GAC2:native-curved-ordered-torsion**
(full ordered nonlinear torsion on the inherited coframe). -/
@[ledger "GAC2:native-curved-ordered-torsion"]
theorem torsionLaw : Statement.torsionLaw := by
  intro K _ _
  exact ⟨original_torsion_all_components,
    original_coframe_metric_inverse,
    original_complete_torsion_density⟩

/-! ## Non-vacuity -/
example : exactTorsionDensity (1 / 2 : ℚ) 1 (5 / 4) (3 / 4) = -1 / 4 := by
  rw [original_complete_torsion_density (1 / 2) 1 (5 / 4) (3 / 4) (by norm_num)
    (by norm_num) (by norm_num)]
  norm_num

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
