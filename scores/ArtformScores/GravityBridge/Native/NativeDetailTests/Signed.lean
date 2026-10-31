import ArtformScores.GravityBridge.Native.NativeDetailTests.SignedStatements

/-! # Signed native rapidity can remove the real stationary branch -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



open CurvedSubdivision

lemma negative_discriminant_has_no_real_stationary_boost (A B C S : ℝ)
    (hD : A ^ 2 - B ^ 2 < 0) (hL : C ^ 2 - S ^ 2 = 1) : A * S + B * C ≠ 0 := by
  intro h
  have he : (A * C + B * S) ^ 2 - (A * S + B * C) ^ 2 = (A ^ 2 - B ^ 2) * (C ^ 2 - S ^ 2) := by ring
  rw [h, hL] at he
  nlinarith [sq_nonneg (A * C + B * S)]

lemma actual_negative_rapidity_discriminant :
    detailD (Real.cosh (Real.log (201 / 202))) (Real.sinh (Real.log (201 / 202))) =
      -151 / 83250381402 := by
  have he : Real.exp (Real.log (201 / 202)) = (201 / 202 : ℝ) := Real.exp_log (by norm_num)
  norm_num [detailD, detailA, detailB, Real.cosh_eq, Real.sinh_eq, Real.exp_neg, he]

lemma original_negative_rapidity_has_no_zero_source_detail (b : ℝ) (hb : b ≠ 0) (r : ℝ) :
    nativeSplitFirst b (Real.log (201 / 202)) r 0 ≠ 0 := by
  have hD : detailD (Real.cosh (Real.log (201 / 202))) (Real.sinh (Real.log (201 / 202))) < 0 := by
    rw [actual_negative_rapidity_discriminant]
    norm_num
  have hn := negative_discriminant_has_no_real_stationary_boost
    (detailA (Real.cosh (Real.log (201 / 202))) (Real.sinh (Real.log (201 / 202))))
    (detailB (Real.sinh (Real.log (201 / 202)))) (Real.cosh r) (Real.sinh r)
    hD (Real.cosh_sq_sub_sinh_sq r)
  rw [(actual_split_force_normal_form b (Real.log (201 / 202)) r 0).1]
  unfold currentDetailForce
  simpa [hb] using mul_ne_zero (neg_ne_zero.mpr hb) hn

lemma actual_negative_branch_point : 0 < (201 / 202 : ℝ) ∧ (201 / 202 : ℝ) < 1 ∧
    Real.log (201 / 202) < 0 := by
  refine ⟨by norm_num, by norm_num, Real.log_neg (by norm_num) (by norm_num)⟩

/-- **GAC2:native-negative-detail-discriminant**
(signed native rapidity can remove the real stationary branch). -/
@[ledger "GAC2:native-negative-detail-discriminant"]
theorem signedLaw : Statement.signedLaw := by
  exact ⟨negative_discriminant_has_no_real_stationary_boost,
    actual_negative_rapidity_discriminant,
    original_negative_rapidity_has_no_zero_source_detail,
    actual_negative_branch_point⟩

/-! ## Non-vacuity -/
example : ∀ r : ℝ, nativeSplitFirst 1 (Real.log (201 / 202)) r 0 ≠ 0 :=
  fun r => original_negative_rapidity_has_no_zero_source_detail 1 (by norm_num) r

end Artform.Scores.GravityBridge.Native.NativeDetailTests
