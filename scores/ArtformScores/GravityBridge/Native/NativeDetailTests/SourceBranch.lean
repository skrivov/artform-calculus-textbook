import ArtformScores.GravityBridge.Native.NativeDetailTests.SourceBranchStatements

/-! # Every real source has one stationary native detail on the positive branch -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



open CurvedSubdivision
noncomputable section

lemma positive_native_detail_root (u : ℝ) (hu : 0 < u) : 0 < detailRoot u := by
  have hs := Real.sinh_pos_iff.mpr hu
  have hc := Real.cosh_sq_sub_sinh_sq u
  have hco : 1 < Real.cosh u := by
    nlinarith [Real.one_le_cosh u, mul_pos hs hs]
  exact Real.sqrt_pos.mpr (actual_detail_root_budget _ _ hc hco hs).1

lemma all_native_detail_Hessians_negative (b u r : ℝ) (hb : 0 < b) (hu : 0 < u) :
    nativeSplitSecond b u r < 0 := by
  have hs := Real.sinh_pos_iff.mpr hu
  have hcr := Real.cosh_pos r
  have hcu := Real.cosh_pos (u + r)
  have he : Real.sinh (u + r) + Real.sinh (u - r) = 2 * Real.sinh u * Real.cosh r := by
    rw [Real.sinh_add, Real.sinh_sub]
    ring
  rw [nativeSplitSecond, he]
  have h1 : 0 < b * (2 * Real.sinh u * Real.cosh r) := by positivity
  have h2 : 0 < (1 / 101 : ℝ) * b * Real.cosh (u + r) := by positivity
  linarith

lemma native_detail_force_strictAnti (b u j : ℝ) (hb : 0 < b) (hu : 0 < u) :
    StrictAnti (fun r => nativeSplitFirst b u r j) :=
  strictAnti_of_hasDerivAt_neg (fun r => actual_split_second_derivative b u r j)
    (fun r => all_native_detail_Hessians_negative b u r hb hu)

lemma actual_native_source_shift (b u r r0 j : ℝ) (hu : 0 < u)
    (hc : Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u))
    (hs : Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u)) :
    nativeSplitFirst b u r j = -b * detailRoot u * Real.sinh (r - r0) - j ∧
    nativeSplitAction b u r j = (1 / 101 : ℝ) * b - b * detailRoot u * Real.cosh (r - r0) - j *
      r := by
  have hR := ne_of_gt (positive_native_detail_root u hu)
  constructor
  · rw [(actual_split_force_normal_form b u r j).1, Real.sinh_sub, hc, hs]
    unfold currentDetailForce stationaryC stationaryS
    change _ = -b * detailRoot u * (Real.sinh r * (detailA (Real.cosh u) (Real.sinh u) /
      detailRoot u)-
      Real.cosh r * (-detailB (Real.sinh u) / detailRoot u)) - j
    field_simp
    ring
  · rw [actual_split_action_normal_form, Real.cosh_sub, hc, hs]
    unfold currentFineValue stationaryC stationaryS
    change _ = (1 / 101 : ℝ) * b - b * detailRoot u *
      (Real.cosh r * (detailA (Real.cosh u) (Real.sinh u) / detailRoot u)-
        Real.sinh r * (-detailB (Real.sinh u) / detailRoot u)) - j * r
    field_simp
    ring

lemma every_real_source_has_unique_native_detail (b u j : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∃! r : ℝ, nativeSplitFirst b u r j = 0 := by
  obtain ⟨r0, hc, hs, _, _⟩ := actual_native_stationary_history b u hu
  have hR := positive_native_detail_root u hu
  have he : sourceRapidity b u r0 j - r0 = -Real.arsinh (j / (b * detailRoot u)) := by
    unfold sourceRapidity
    ring
  have hz : nativeSplitFirst b u (sourceRapidity b u r0 j) j = 0 := by
    rw [(actual_native_source_shift b u _ r0 j hu hc hs).1, he, Real.sinh_neg, Real.sinh_arsinh]
    field_simp
    ring
  refine ⟨sourceRapidity b u r0 j, hz, ?_⟩
  intro r hr
  exact (native_detail_force_strictAnti b u j hb hu).injective (hr.trans hz.symm)

/-- **GAC2:native-global-source-detail**
(every real source has one stationary native detail on the positive branch). -/
@[ledger "GAC2:native-global-source-detail"]
theorem sourceBranchLaw : Statement.sourceBranchLaw := by
  exact ⟨positive_native_detail_root,
    all_native_detail_Hessians_negative,
    native_detail_force_strictAnti,
    actual_native_source_shift,
    every_real_source_has_unique_native_detail⟩

/-! ## Non-vacuity -/
example : ∃! r : ℝ, nativeSplitFirst 1 (Real.log 2) r 7 = 0 :=
  every_real_source_has_unique_native_detail 1 (Real.log 2) 7 (by norm_num)
    (Real.log_pos (by norm_num))
end

end Artform.Scores.GravityBridge.Native.NativeDetailTests
