import ArtformScores.GravityBridge.Native.CurvedSubdivision.DetailStatements

/-! # Corrected stationary real detail in the original split action -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40



noncomputable section

lemma proper_boost_real_rapidity (C S : ℝ) (hC : 0 < C) (hL : C ^ 2 - S ^ 2 = 1) :
    ∃ r : ℝ, Real.cosh r = C ∧ Real.sinh r = S := by
  have hq : 0 < C + S := by
    by_contra h
    have hle : C + S ≤ 0 := le_of_not_gt h
    have hp := mul_nonneg (by linarith : 0 ≤ -C - S) (by linarith : 0 ≤ C - S)
    nlinarith
  have hm : (C + S) * (C - S) = 1 := by linear_combination hL
  have hi : (C + S)⁻¹ = C - S := by
    apply mul_left_cancel₀ (ne_of_gt hq)
    rw [mul_inv_cancel₀ (ne_of_gt hq), hm]
  refine ⟨Real.log (C + S), ?_, ?_⟩
  · rw [Real.cosh_eq, Real.exp_log hq, Real.exp_neg, Real.exp_log hq, hi]
    ring
  · rw [Real.sinh_eq, Real.exp_log hq, Real.exp_neg, Real.exp_log hq, hi]
    ring

lemma actual_split_force_normal_form (b u r j : ℝ) :
    nativeSplitFirst b u r j =
      currentDetailForce b (Real.cosh u) (Real.sinh u) (Real.cosh r) (Real.sinh r) j ∧
    nativeSplitSecond b u r =
      currentDetailHessian b (Real.cosh u) (Real.sinh u) (Real.cosh r) (Real.sinh r) := by
  constructor
  · dsimp only [nativeSplitFirst, currentDetailForce, detailA, detailB]
    rw [Real.cosh_add, Real.cosh_sub, Real.sinh_add]
    ring
  · dsimp only [nativeSplitSecond, currentDetailHessian, detailA, detailB]
    rw [Real.sinh_add, Real.sinh_sub, Real.cosh_add]
    ring

lemma actual_split_action_normal_form (b u r j : ℝ) :
    nativeSplitAction b u r j =
      currentFineValue b (Real.cosh u) (Real.sinh u) (Real.cosh r) (Real.sinh r) - j * r := by
  dsimp only [nativeSplitAction, currentFineValue, detailA, detailB]
  rw [Real.sinh_add, Real.sinh_sub, Real.cosh_add]
  ring

lemma actual_native_stationary_history (b u : ℝ) (hu : 0 < u) :
    ∃ r : ℝ, Real.cosh r = stationaryC (Real.cosh u) (Real.sinh u) ∧
      Real.sinh r = stationaryS (Real.cosh u) (Real.sinh u) ∧
      nativeSplitFirst b u r 0 = 0 ∧
      nativeSplitSecond b u r = -b * Real.sqrt (detailD (Real.cosh u) (Real.sinh u)) := by
  have hs := Real.sinh_pos_iff.mpr hu
  have hc := Real.cosh_sq_sub_sinh_sq u
  have hco : 1 < Real.cosh u := by
    have h1 := Real.one_le_cosh u
    nlinarith [mul_pos hs hs]
  have hp := actual_stationary_proper_boost (Real.cosh u) (Real.sinh u) hc hco hs
  obtain ⟨r, hrc, hrs⟩ := proper_boost_real_rapidity _ _ hp.1 hp.2
  have he := actual_stationary_current_return b (Real.cosh u) (Real.sinh u) hc hco hs
  refine ⟨r, hrc, hrs, ?_, ?_⟩
  · rw [(actual_split_force_normal_form b u r 0).1, hrc, hrs]
    exact he.1
  · rw [(actual_split_force_normal_form b u r 0).2, hrc, hrs]
    exact he.2.1

lemma stationary_history_same_rapidity_guard (u r : ℝ) (hu : 0 < u)
    (hrc : Real.cosh r = stationaryC (Real.cosh u) (Real.sinh u))
    (hrs : Real.sinh r = stationaryS (Real.cosh u) (Real.sinh u)) :
    -u < r ∧ r < 0 := by
  have hs := Real.sinh_pos_iff.mpr hu
  have hc := Real.cosh_sq_sub_sinh_sq u
  have hco : 1 < Real.cosh u := by
    nlinarith [Real.one_le_cosh u, mul_pos hs hs]
  have hd := (actual_detail_root_budget (Real.cosh u) (Real.sinh u) hc hco hs).1
  have hR : 0 < Real.sqrt (detailD (Real.cosh u) (Real.sinh u)) := Real.sqrt_pos.mpr hd
  have hn : Real.sinh r < 0 := by
    rw [hrs]
    unfold stationaryS detailB
    exact div_neg_of_neg_of_pos (by linarith) hR
  have hp : Real.sinh (u + r) = 2 * (Real.sinh u) ^ 2 /
      Real.sqrt (detailD (Real.cosh u) (Real.sinh u)) := by
    rw [Real.sinh_add, hrc, hrs]
    unfold stationaryC stationaryS detailA detailB
    ring
  have hupr : 0 < u + r := by
    apply Real.sinh_pos_iff.mp
    rw [hp]
    positivity
  exact ⟨by linarith, Real.sinh_neg_iff.mp hn⟩

lemma actual_original_stationary_detail (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∃ r : ℝ, -u < r ∧ r < 0 ∧ nativeSplitFirst b u r 0 = 0 ∧
      literalTwoChildAction b u r = stationaryValue b (Real.cosh u) (Real.sinh u) := by
  obtain ⟨r, hrc, hrs, hforce, _⟩ := actual_native_stationary_history b u hu
  have hbound := stationary_history_same_rapidity_guard u r hu hrc hrs
  have hs := Real.sinh_pos_iff.mpr hu
  have hc := Real.cosh_sq_sub_sinh_sq u
  have hco : 1 < Real.cosh u := by
    nlinarith [Real.one_le_cosh u, mul_pos hs hs]
  refine ⟨r, hbound.1, hbound.2, hforce, ?_⟩
  have he := full_original_split_source_binding b u r 0 (ne_of_gt hb)
  simp only [zero_mul, sub_zero] at he
  rw [he, actual_split_action_normal_form, zero_mul, sub_zero, hrc, hrs]
  exact (actual_stationary_current_return b (Real.cosh u) (Real.sinh u) hc hco hs).2.2

lemma actual_original_stationary_derivative (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∃ r : ℝ, -u < r ∧ r < 0 ∧ HasDerivAt (literalTwoChildAction b u) 0 r ∧
      literalTwoChildAction b u r = stationaryValue b (Real.cosh u) (Real.sinh u) := by
  obtain ⟨r, hlo, hhi, hforce, hvalue⟩ := actual_original_stationary_detail b u hb hu
  have he : literalTwoChildAction b u = fun x => nativeSplitAction b u x 0 := by
    funext x
    simpa using full_original_split_source_binding b u x 0 (ne_of_gt hb)
  refine ⟨r, hlo, hhi, ?_, hvalue⟩
  rw [he]
  simpa only [hforce] using actual_split_first_derivative b u r 0

/-- **GAC2:native-current-stationary-detail**
(corrected stationary real detail in the original split action). -/
@[ledger "GAC2:native-current-stationary-detail"]
theorem detailLaw : Statement.detailLaw := by
  exact ⟨proper_boost_real_rapidity,
    actual_split_force_normal_form,
    actual_split_action_normal_form,
    actual_native_stationary_history,
    stationary_history_same_rapidity_guard,
    actual_original_stationary_detail,
    actual_original_stationary_derivative,
    old_symmetric_detail_not_stationary,
    actual_split_first_derivative,
    actual_split_second_derivative,
    actual_detail_root_budget⟩

/-! ## Non-vacuity -/
example : ∃ r : ℝ, nativeSplitFirst 1 (Real.log 2) r 0 = 0 := by
  obtain ⟨r, _, _, hr, _⟩ := actual_native_stationary_history 1 (Real.log 2)
    (Real.log_pos (by norm_num))
  exact ⟨r, hr⟩
end

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
