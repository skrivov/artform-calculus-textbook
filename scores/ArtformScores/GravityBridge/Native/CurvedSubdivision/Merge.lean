import ArtformScores.GravityBridge.Native.CurvedSubdivision.MergeStatements

/-! # Corrected stationary native merge still differs from the parent -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40



noncomputable section

lemma corrected_stationary_native_merge_still_differs (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∃ r : ℝ, -u < r ∧ r < 0 ∧ nativeSplitFirst b u r 0 = 0 ∧
      0 < literalTwoChildAction b u r-
        fullOriginalCell 1 b 1 0 (Real.cosh (2 * u)) (Real.sinh (2 * u)) := by
  obtain ⟨r, hrlo, hrhi, hforce, hval⟩ := actual_original_stationary_detail b u hb hu
  have hs := Real.sinh_pos_iff.mpr hu
  have hc := Real.cosh_sq_sub_sinh_sq u
  have hco : 1 < Real.cosh u := by
    nlinarith [Real.one_le_cosh u, mul_pos hs hs]
  have hdiff := stationary_merge_strict_defect b (Real.cosh u) (Real.sinh u) hb hc hco hs
  refine ⟨r, hrlo, hrhi, hforce, ?_⟩
  rw [hval, complete_original_cell_value 1 b 1 0 (Real.cosh (2 * u)) (Real.sinh (2 * u))
    (by norm_num) (ne_of_gt hb) (by norm_num), Real.sinh_two_mul]
  nlinarith

lemma same_small_log_guard_for_corrected_children (delta : ℝ) (hd : 0 < delta) :
    ∃ u r : ℝ, 0 < u ∧ 2 * u < delta ∧ 0 < u + r ∧ u + r < delta ∧
      0 < u - r ∧ u - r < delta ∧ nativeSplitFirst 1 u r 0 = 0 ∧
      0 < literalTwoChildAction 1 u r-
        fullOriginalCell 1 1 1 0 (Real.cosh (2 * u)) (Real.sinh (2 * u)) := by
  let u := delta / 3
  have hu : 0 < u := by dsimp [u];positivity
  obtain ⟨r, hlo, hhi, hforce, hdiff⟩ := corrected_stationary_native_merge_still_differs 1 u
    (by norm_num) hu
  refine ⟨u, r, hu, ?_, ?_, ?_, ?_, ?_, hforce, hdiff⟩ <;> dsimp [u] at * <;> linarith

/-- **GAC2:native-stationary-merge-defect**
(corrected stationary native merge still differs from the parent). -/
@[ledger "GAC2:native-stationary-merge-defect"]
theorem mergeLaw : Statement.mergeLaw := by
  exact ⟨corrected_stationary_native_merge_still_differs,
    same_small_log_guard_for_corrected_children,
    stationary_merge_exact_defect⟩

/-! ## Non-vacuity -/
example : ∃ u r : ℝ, 0 < u ∧ 2 * u < (1 / 100 : ℝ) ∧ 0 < u + r ∧ u + r < 1 / 100 ∧
    0 < u - r ∧ u - r < 1 / 100 ∧ nativeSplitFirst 1 u r 0 = 0 ∧
    0 < literalTwoChildAction 1 u r-
      fullOriginalCell 1 1 1 0 (Real.cosh (2 * u)) (Real.sinh (2 * u)) :=
  same_small_log_guard_for_corrected_children (1 / 100) (by norm_num)
end

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
