import ArtformScores.GravityBridge.Native.NativeDetailTests.CoframeStatements

/-! # Connection detail source leaves the complete coframe covector -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



open CurvedSubdivision Filter
noncomputable section

lemma native_coframe_density_negative (u r : ℝ) (hu : 0 < u) : nativeCoframeDensity u r < 0 := by
  obtain ⟨r0, hc, hs, _, _⟩ := actual_native_stationary_history 1 u hu
  have hshift := (actual_native_source_shift 1 u r r0 0 hu hc hs).2
  have hcosh := Real.one_le_cosh (r - r0)
  have hR := positive_native_detail_root u hu
  have hLor := Real.cosh_sq_sub_sinh_sq u
  have hsu := Real.sinh_pos_iff.mpr hu
  have hco : 1 < Real.cosh u := by
    nlinarith [Real.one_le_cosh u, mul_pos hsu hsu]
  have hp := (actual_detail_root_budget _ _ hLor hco hsu).2
  unfold nativeCoframeDensity
  rw [hshift]
  simp only [mul_one, one_mul, zero_mul, sub_zero]
  change (1 / 101 : ℝ) < detailRoot u at hp
  nlinarith

lemma literal_coframe_source_for_every_detail (b u r j : ℝ) (hb : b ≠ 0) :
    HasDerivAt (fun x => literalTwoChildAction x u r - j * r) (nativeCoframeDensity u r) b := by
  have he : (fun x => literalTwoChildAction x u r - j * r) =ᶠ[nhds b]
      (fun x => x * nativeCoframeDensity u r - j * r) := by
    filter_upwards [eventually_ne_nhds hb] with x hx
    rw [full_original_split_source_binding x u r j hx]
    unfold nativeCoframeDensity nativeSplitAction
    ring
  simpa only [one_mul] using
    (((hasDerivAt_id b).mul_const (nativeCoframeDensity u r)).sub_const (j *
      r)).congr_of_eventuallyEq he

lemma original_detail_source_does_not_repair_coframe (b u r j : ℝ) (hb : 0 < b) (hu : 0 < u) :
    HasDerivAt (fun x => literalTwoChildAction x u r - j * r) (nativeCoframeDensity u r) b ∧
      nativeCoframeDensity u r < 0 :=
  ⟨literal_coframe_source_for_every_detail b u r j (ne_of_gt hb),
    native_coframe_density_negative u r hu⟩

lemma actual_zero_source_action_negative (b u r : ℝ) (hb : 0 < b) (hu : 0 < u) :
    nativeSplitAction b u r 0 < 0 := by
  have he : nativeSplitAction b u r 0 = b * nativeCoframeDensity u r := by
    dsimp [nativeCoframeDensity, nativeSplitAction]
    ring
  rw [he]
  exact mul_neg_of_pos_of_neg hb (native_coframe_density_negative u r hu)

/-- **GAC2:native-all-detail-coframe-source**
(connection detail source leaves the complete coframe covector). -/
@[ledger "GAC2:native-all-detail-coframe-source"]
theorem coframeLaw : Statement.coframeLaw := by
  exact ⟨native_coframe_density_negative,
    literal_coframe_source_for_every_detail,
    original_detail_source_does_not_repair_coframe,
    actual_zero_source_action_negative⟩

/-! ## Non-vacuity -/
example : nativeCoframeDensity (Real.log 2) 7 < 0 :=
  native_coframe_density_negative (Real.log 2) 7 (Real.log_pos (by norm_num))
end

end Artform.Scores.GravityBridge.Native.NativeDetailTests
