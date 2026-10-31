import ArtformScores.GravityBridge.Native.NativeDetailTests.EnvelopeStatements

/-! # Original source envelope retains its derivative and susceptibility -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



open CurvedSubdivision
noncomputable section

lemma native_source_rapidity_derivative (b u r0 j : ℝ) :
    HasDerivAt (sourceRapidity b u r0) (sourceSlope b u j) j := by
  have h := ((Real.hasDerivAt_arsinh (j / (b * detailRoot u))).comp j
    ((hasDerivAt_id j).div_const (b * detailRoot u))).const_sub r0
  convert h using 1
  · rfl
  · dsimp [sourceSlope]
    ring

lemma full_original_envelope_binding (b u r0 j : ℝ) (hb : b ≠ 0) (hu : 0 < u)
    (hc : Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u))
    (hs : Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u)) :
    literalTwoChildAction b u (sourceRapidity b u r0 j) - j * sourceRapidity b u r0 j =
      nativeEnvelope b u r0 j := by
  rw [full_original_split_source_binding _ _ _ _ hb,
    (actual_native_source_shift b u _ r0 j hu hc hs).2]
  rfl

lemma actual_source_envelope_derivative (b u r0 j : ℝ) (hb : 0 < b) (hu : 0 < u) :
    HasDerivAt (nativeEnvelope b u r0) (-sourceRapidity b u r0 j) j := by
  have hd := mul_pos hb (positive_native_detail_root u hu)
  have hroot := ne_of_gt (positive_native_detail_root u hu)
  have hr := native_source_rapidity_derivative b u r0 j
  have hc := (Real.hasDerivAt_cosh (sourceRapidity b u r0 j - r0)).comp j (hr.sub_const r0)
  have h := ((hasDerivAt_const j ((1 / 101 : ℝ) * b)).sub (hc.const_mul (b * detailRoot u))).sub
    ((hasDerivAt_id j).mul hr)
  have he : sourceRapidity b u r0 j - r0 = -Real.arsinh (j / (b * detailRoot u)) := by
    unfold sourceRapidity
    ring
  have hf : b * detailRoot u * Real.sinh (sourceRapidity b u r0 j - r0) + j = 0 := by
    rw [he, Real.sinh_neg, Real.sinh_arsinh]
    field_simp [ne_of_gt hb, hroot]
    ring
  convert h using 1
  · rfl
  · simp only [zero_sub, one_mul, id_eq]
    linear_combination (sourceSlope b u j) * hf

lemma actual_source_envelope_second (b u r0 j : ℝ) :
    HasDerivAt (fun x => -sourceRapidity b u r0 x)
      ((Real.sqrt (1 + (j / (b * detailRoot u)) ^ 2))⁻¹ / (b * detailRoot u)) j := by
  convert (native_source_rapidity_derivative b u r0 j).neg using 1
  unfold sourceSlope
  ring

lemma actual_source_susceptibility_positive (b u j : ℝ) (hb : 0 < b) (hu : 0 < u) :
    0 < (Real.sqrt (1 + (j / (b * detailRoot u)) ^ 2))⁻¹ / (b * detailRoot u) := by
  have hd := mul_pos hb (positive_native_detail_root u hu)
  have hsq : 0 < 1 + (j / (b * detailRoot u)) ^ 2 := by positivity
  exact div_pos (inv_pos.mpr (Real.sqrt_pos.mpr hsq)) hd

lemma omitting_source_changes_zero_source_covector (b u r0 : ℝ) (hb : 0 < b) (hu : 0 < u) :
    HasDerivAt (rawEnvelope b u r0) 0 0 ∧
      HasDerivAt (nativeEnvelope b u r0) (-r0) 0 := by
  have hr := native_source_rapidity_derivative b u r0 0
  have hc := ((Real.hasDerivAt_cosh (sourceRapidity b u r0 0 - r0)).comp 0
    (hr.sub_const r0)).const_mul (b * detailRoot u)
  constructor
  · convert (hasDerivAt_const 0 ((1 / 101 : ℝ) * b)).sub hc using 1
    · rfl
    · norm_num [sourceRapidity]
  · simpa [sourceRapidity] using actual_source_envelope_derivative b u r0 0 hb hu

lemma original_zero_source_covector_mismatch (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∃ r0 : ℝ, Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u) ∧
      Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u) ∧ r0 < 0 ∧
      HasDerivAt (rawEnvelope b u r0) 0 0 ∧
      HasDerivAt (nativeEnvelope b u r0) (-r0) 0 ∧ 0 < -r0 := by
  obtain ⟨r0, hc, hs, _, _⟩ := actual_native_stationary_history b u hu
  have hr := (stationary_history_same_rapidity_guard u r0 hu hc hs).2
  have hd := omitting_source_changes_zero_source_covector b u r0 hb hu
  exact ⟨r0, hc, hs, hr, hd.1, hd.2, by linarith⟩

/-- **GAC2:native-source-envelope-contacts**
(original source envelope retains its derivative and susceptibility). -/
@[ledger "GAC2:native-source-envelope-contacts"]
theorem envelopeLaw : Statement.envelopeLaw := by
  exact ⟨native_source_rapidity_derivative,
    full_original_envelope_binding,
    actual_source_envelope_derivative,
    actual_source_envelope_second,
    actual_source_susceptibility_positive,
    omitting_source_changes_zero_source_covector,
    original_zero_source_covector_mismatch⟩

/-! ## Non-vacuity -/
example : ∃ r0 : ℝ, r0 < 0 ∧ HasDerivAt (rawEnvelope 1 (Real.log 2) r0) 0 0 ∧
    HasDerivAt (nativeEnvelope 1 (Real.log 2) r0) (-r0) 0 := by
  obtain ⟨r0, _, hr, _, _⟩ := actual_original_stationary_detail 1 (Real.log 2)
    (by norm_num) (Real.log_pos (by norm_num))
  exact ⟨r0, hr, omitting_source_changes_zero_source_covector 1 (Real.log 2) r0
    (by norm_num) (Real.log_pos (by norm_num))⟩
end

end Artform.Scores.GravityBridge.Native.NativeDetailTests
