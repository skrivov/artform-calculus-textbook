import ArtformScores.GravityBridge.Native.NativeDetailTests.FiniteWindowStatements

/-! # Bounded native detail interval has explicit finite positive mass -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



open CurvedSubdivision MeasureTheory Set
noncomputable section

lemma actual_bounded_detail_density (b u r r0 L : ℝ) (hb : 0 < b) (hu : 0 < u) (hL : 0 ≤ L)
    (hc : Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u))
    (hs : Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u)) (hr : |r - r0| ≤ L) :
    positiveRealWeight b u r ≤ boundedWeightCeiling b u L := by
  have hcosh : Real.cosh (r - r0) ≤ Real.cosh L := Real.cosh_le_cosh.mpr (by
    simpa [abs_of_nonneg hL] using hr)
  have hd := mul_pos hb (positive_native_detail_root u hu)
  have he := (actual_native_source_shift b u r r0 0 hu hc hs).2
  have harg : -nativeSplitAction b u r 0 ≤ b * detailRoot u * Real.cosh L - (1 / 101 : ℝ) * b := by
    rw [he]
    nlinarith
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr harg)

lemma actual_finite_window_mass_bound (b u r0 L : ℝ) (hb : 0 < b) (hu : 0 < u) (hL : 0 ≤ L)
    (hc : Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u))
    (hs : Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u)) :
    (∫⁻ r in Icc (r0 - L) (r0 + L), positiveRealWeight b u r) ≤
      boundedWeightCeiling b u L * ENNReal.ofReal (2 * L) := by
  have hm : (∫⁻ r in Icc (r0 - L) (r0 + L), positiveRealWeight b u r) ≤
      ∫⁻ _ in Icc (r0 - L) (r0 + L), boundedWeightCeiling b u L := by
    apply setLIntegral_mono' measurableSet_Icc
    intro r hr
    apply actual_bounded_detail_density b u r r0 L hb hu hL hc hs
    exact abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
  rw [setLIntegral_const, Real.volume_Icc] at hm
  have he : (r0 + L) - (r0 - L) = 2 * L := by ring
  simpa only [he] using hm

lemma actual_finite_positive_window_mass (b u r0 L : ℝ) (hb : 0 < b) (hu : 0 < u) (hL : 0 < L)
    (hc : Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u))
    (hs : Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u)) :
    0 < (∫⁻ r in Icc (r0 - L) (r0 + L), positiveRealWeight b u r) ∧
      (∫⁻ r in Icc (r0 - L) (r0 + L), positiveRealWeight b u r) < ∞ := by
  have hm := actual_finite_window_mass_bound b u r0 L hb hu hL.le hc hs
  have hf : boundedWeightCeiling b u L * ENNReal.ofReal (2 * L) < ∞ := by
    unfold boundedWeightCeiling
    finiteness
  have hl : (∫⁻ _ in Icc (r0 - L) (r0 + L), (1 : ℝ≥0∞)) ≤
      ∫⁻ r in Icc (r0 - L) (r0 + L), positiveRealWeight b u r :=
    lintegral_mono (fun r => actual_native_zero_source_weight_lower b u r hb hu)
  rw [setLIntegral_one, Real.volume_Icc] at hl
  have he : (r0 + L) - (r0 - L) = 2 * L := by ring
  rw [he] at hl
  exact ⟨lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by linarith)) hl, lt_of_le_of_lt hm hf⟩

/-- **GAC2:native-finite-detail-weight**
(bounded native detail interval has explicit finite positive mass). -/
@[ledger "GAC2:native-finite-detail-weight"]
theorem finiteWindowLaw : Statement.finiteWindowLaw := by
  exact ⟨actual_bounded_detail_density,
    actual_finite_window_mass_bound,
    actual_finite_positive_window_mass⟩

/-! ## Non-vacuity -/
example : ∃ r0 : ℝ, 0 < (∫⁻ r in Icc (r0 - 1) (r0 + 1), positiveRealWeight 1 (Real.log 2) r) ∧
    (∫⁻ r in Icc (r0 - 1) (r0 + 1), positiveRealWeight 1 (Real.log 2) r) < ∞ := by
  obtain ⟨r0, hc, hs, _, _⟩ := actual_native_stationary_history 1 (Real.log 2)
    (Real.log_pos (by norm_num))
  exact ⟨r0, actual_finite_positive_window_mass 1 (Real.log 2) r0 1 (by norm_num)
    (Real.log_pos (by norm_num)) (by norm_num) hc hs⟩
end

end Artform.Scores.GravityBridge.Native.NativeDetailTests
