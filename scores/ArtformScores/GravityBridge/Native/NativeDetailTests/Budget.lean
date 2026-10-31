import ArtformScores.GravityBridge.Native.NativeDetailTests.BudgetStatements

/-! # Small native value defect does not supply a derivative budget -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



open CurvedSubdivision
noncomputable section

lemma exact_effective_defect_budget (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    0 < effectiveMergeDefect b u ∧ effectiveMergeDefect b u < 202 * b * (Real.sinh u) ^ 4 := by
  have hc := Real.cosh_sq_sub_sinh_sq u
  have hs := Real.sinh_pos_iff.mpr hu
  have hco : 1 < Real.cosh u := by
    nlinarith [Real.one_le_cosh u, mul_pos hs hs]
  have hR := (actual_detail_root_budget _ _ hc hco hs).2
  have he := stationary_merge_exact_defect b (Real.cosh u) (Real.sinh u) hc hco hs
  have hp := stationary_merge_strict_defect b (Real.cosh u) (Real.sinh u) hb hc hco hs
  have hcs : 0 < 2 * Real.cosh u * Real.sinh u := by positivity
  unfold effectiveMergeDefect
  rw [Real.sinh_two_mul]
  constructor
  · nlinarith
  · nlinarith [mul_pos hp (show 0 < (1 / 101 : ℝ) + 2 * Real.cosh u * Real.sinh u +
      Real.sqrt (detailD (Real.cosh u) (Real.sinh u)) - (2 / 101 : ℝ) by linarith)]

lemma original_sinh_budget (u delta : ℝ) (hu : 0 < u) (hd : u ≤ delta) :
    Real.sinh u ≤ u * Real.cosh delta := by
  obtain ⟨v, hv, he⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh hu
    Real.continuous_sinh.continuousOn (fun x _ => Real.hasDerivAt_sinh x)
  have hc : Real.cosh v ≤ Real.cosh delta := Real.cosh_le_cosh.mpr (by
    rw [abs_of_pos hv.1, abs_of_pos (lt_of_lt_of_le hu hd)]
    exact le_trans hv.2.le hd)
  have heq : Real.sinh u = Real.cosh v * u := by
    simp only [Real.sinh_zero, sub_zero] at he
    exact (eq_div_iff (ne_of_gt hu)).mp he |>.symm
  rw [heq]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right hc hu.le

lemma native_small_rapidity_quartic_budget (b u delta : ℝ) (hb : 0 < b) (hu : 0 < u)
    (hd : u ≤ delta) :
    0 < effectiveMergeDefect b u ∧
      effectiveMergeDefect b u < 202 * b * (Real.cosh delta) ^ 4 * u ^ 4 := by
  have h := exact_effective_defect_budget b u hb hu
  refine ⟨h.1, lt_of_lt_of_le h.2 ?_⟩
  calc
    202 * b * (Real.sinh u) ^ 4 ≤ 202 * b * (u * Real.cosh delta) ^ 4 := by
      gcongr
      exact original_sinh_budget u delta hu hd
    _ = 202 * b * (Real.cosh delta) ^ 4 * u ^ 4 := by ring

lemma native_step_scaled_defect_budget (b h v delta : ℝ) (hb : 0 < b) (hh : 0 < h)
    (hv : 0 < v) (hd : h * v ≤ delta) :
    0 < effectiveMergeDefect b (h * v) ∧
      effectiveMergeDefect b (h * v) < 202 * b * (Real.cosh delta) ^ 4 * h ^ 4 * v ^ 4 := by
  have ht := native_small_rapidity_quartic_budget b (h * v) delta hb (mul_pos hh hv) hd
  refine ⟨ht.1, ?_⟩
  calc
    _ < 202 * b * (Real.cosh delta) ^ 4 * (h * v) ^ 4 := ht.2
    _ = 202 * b * (Real.cosh delta) ^ 4 * h ^ 4 * v ^ 4 := by ring

lemma actual_literal_stationary_defect_binding (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∃ r : ℝ, -u < r ∧ r < 0 ∧ HasDerivAt (literalTwoChildAction b u) 0 r ∧
      literalTwoChildAction b u r-
        fullOriginalCell 1 b 1 0 (Real.cosh (2 * u)) (Real.sinh (2 * u)) = effectiveMergeDefect
          b u := by
  obtain ⟨r, hl, hr, hd, hv⟩ := actual_original_stationary_derivative b u hb hu
  refine ⟨r, hl, hr, hd, ?_⟩
  rw [hv, complete_original_cell_value 1 b 1 0 (Real.cosh (2 * u)) (Real.sinh (2 * u))
    (by norm_num) (ne_of_gt hb) (by norm_num)]
  unfold effectiveMergeDefect
  ring

lemma actual_half_detail_source (b u : ℝ) :
    nativeSplitFirst b u (-u / 2) 0 = b * Real.sinh (u / 2) * (2 * Real.sinh u - (1 / 101 : ℝ))
      := by
  have hf (r : ℝ) : nativeSplitFirst b u r 0 =
      -2 * b * Real.sinh u * Real.sinh r - (1 / 101 : ℝ) * b * Real.sinh (u + r) := by
    unfold nativeSplitFirst
    rw [Real.cosh_add, Real.cosh_sub]
    ring
  rw [hf, show u + (-u / 2) = u / 2 by ring, show -u / 2 = -(u / 2) by ring, Real.sinh_neg]
  ring

lemma small_native_stationary_detail_near_left_endpoint (b u r : ℝ)
    (hb : 0 < b) (hu : 0 < u) (hs : 2 * Real.sinh u < (1 / 101 : ℝ))
    (hr : nativeSplitFirst b u r 0 = 0) : r < -u / 2 := by
  have hn : nativeSplitFirst b u (-u / 2) 0 < 0 := by
    rw [actual_half_detail_source]
    exact mul_neg_of_pos_of_neg (mul_pos hb (Real.sinh_pos_iff.mpr (by linarith)))
      (by linarith)
  by_contra h
  have hh := (native_detail_force_strictAnti b u 0 hb hu).antitone (le_of_not_gt h)
  rw [hr] at hh
  linarith

lemma declared_log_report_second_difference_lower (b h v r : ℝ)
    (hb : 0 < b) (hh : 0 < h) (hv : 0 < v)
    (hs : 2 * Real.sinh (h ^ 2 * v) < (1 / 101 : ℝ))
    (hr : nativeSplitFirst b (h ^ 2 * v) r 0 = 0) :
    4 * v / h < |physicalSecondDifference h (h ^ 2 * v) r| := by
  have hu : 0 < h ^ 2 * v := mul_pos (sq_pos_of_pos hh) hv
  have hlo := small_native_stationary_detail_near_left_endpoint b (h ^ 2 * v) r hb hu hs hr
  have he : physicalSecondDifference h (h ^ 2 * v) r = 8 * r / h ^ 3 := by
    unfold physicalSecondDifference
    field_simp
    ring
  rw [he, abs_div, abs_of_neg (by linarith : 8 * r < 0), abs_of_pos (pow_pos hh 3)]
  apply (div_lt_div_iff₀ hh (pow_pos hh 3)).mpr
  have hscale : 4 * h ^ 2 * v < -(8 * r) := by linarith
  have hm := mul_lt_mul_of_pos_right hscale hh
  nlinarith

/-- **GAC2:native-stationary-value-trace-budget**
(small native value defect does not supply a derivative budget). -/
@[ledger "GAC2:native-stationary-value-trace-budget"]
theorem budgetLaw : Statement.budgetLaw := by
  exact ⟨exact_effective_defect_budget,
    original_sinh_budget,
    native_small_rapidity_quartic_budget,
    native_step_scaled_defect_budget,
    actual_literal_stationary_defect_binding,
    actual_half_detail_source,
    small_native_stationary_detail_near_left_endpoint,
    declared_log_report_second_difference_lower⟩

/-! ## Non-vacuity -/
example : 0 < effectiveMergeDefect 1 (Real.log 2) ∧
    effectiveMergeDefect 1 (Real.log 2) < 202 * (Real.sinh (Real.log 2)) ^ 4 := by
  simpa using exact_effective_defect_budget 1 (Real.log 2) (by norm_num)
    (Real.log_pos (by norm_num))
end

end Artform.Scores.GravityBridge.Native.NativeDetailTests
