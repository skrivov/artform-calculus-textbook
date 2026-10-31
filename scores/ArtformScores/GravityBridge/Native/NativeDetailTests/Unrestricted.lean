import ArtformScores.GravityBridge.Native.NativeDetailTests.UnrestrictedStatements

/-! # Unrestricted positive real weight is not a finite normalization -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



open CurvedSubdivision MeasureTheory
noncomputable section

lemma original_positive_weight_continuous (b u : ℝ) : Continuous (positiveRealWeight b u) := by
  unfold positiveRealWeight
  apply ENNReal.continuous_ofReal.comp
  unfold nativeSplitAction
  fun_prop

lemma actual_native_zero_source_weight_lower (b u r : ℝ) (hb : 0 < b) (hu : 0 < u) :
    1 ≤ positiveRealWeight b u r := by
  have h := actual_zero_source_action_negative b u r hb hu
  have he : 1 ≤ Real.exp (-nativeSplitAction b u r 0) := by
    have hh := Real.exp_le_exp.mpr (show 0 ≤ -nativeSplitAction b u r 0 by linarith)
    simpa using hh
  change (1 : ℝ≥0∞) ≤ ENNReal.ofReal _
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal he

lemma unrestricted_positive_real_integral_infinite (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    (∫⁻ r : ℝ, positiveRealWeight b u r) = ∞ := by
  have hi : (∫⁻ _ : ℝ, (1 : ℝ≥0∞)) ≤ ∫⁻ r : ℝ, positiveRealWeight b u r :=
    lintegral_mono (fun r => actual_native_zero_source_weight_lower b u r hb hu)
  have hc : (∫⁻ _ : ℝ, (1 : ℝ≥0∞)) = ∞ := by
    simp [lintegral_const]
  rw [hc] at hi
  exact top_unique hi

/-- **GAC2:native-unrestricted-positive-weight**
(unrestricted positive real weight is not a finite normalization). -/
@[ledger "GAC2:native-unrestricted-positive-weight"]
theorem unrestrictedLaw : Statement.unrestrictedLaw := by
  exact ⟨original_positive_weight_continuous,
    actual_native_zero_source_weight_lower,
    unrestricted_positive_real_integral_infinite⟩

/-! ## Non-vacuity -/
example : (∫⁻ r : ℝ, positiveRealWeight 1 (Real.log 2) r) = ∞ :=
  unrestricted_positive_real_integral_infinite 1 (Real.log 2) (by norm_num)
    (Real.log_pos (by norm_num))
end

end Artform.Scores.GravityBridge.Native.NativeDetailTests
