import ArtformScores.GravityBridge.Native.Full40.TemporalProfileStatements
/-! # Higher temporal Lorentz jets with explicit real profile bounds -/
namespace Artform.Scores.GravityBridge.Native.Full40
lemma temporal_profile_cut (h c : ℝ) : temporalGaugeProfile h c 0 = 0 := by
  simp [temporalGaugeProfile]
lemma temporal_profile_value (h c : ℝ) (hh : h ≠ 0) : temporalGaugeProfile h c h = c := by
  simp [temporalGaugeProfile, hh]
lemma temporal_profile_derivative (h c : ℝ) :
    HasDerivAt (temporalGaugeProfile h c) 0 0 := by
  convert (((hasDerivAt_id (0 : ℝ)).div_const h).pow 2).const_mul c using 1 <;>
    simp
  all_goals rfl
lemma temporal_log_adjustment (h c : ℝ) (hh : h ≠ 0) :
    temporalGaugeProfile h (-c) h - temporalGaugeProfile h (-c) 0 = -c := by
  rw [temporal_profile_value h (-c) hh, temporal_profile_cut]
  ring
lemma temporal_physical_adjustment (h c : ℝ) (hh : h ≠ 0) :
    -(temporalGaugeProfile h (-c) h - temporalGaugeProfile h (-c) 0) / h = c / h := by
  rw [temporal_log_adjustment h c hh]
  ring
lemma leading_scaled_profile (h a : ℝ) (hh : h ≠ 0) (t : ℝ) :
    temporalGaugeProfile h (h ^ 3 * a / 4) t = h * a * t ^ 2 / 4 := by
  unfold temporalGaugeProfile
  field_simp
lemma no_forward_frame_preserving_adjustment (h c : ℝ)
    (g : ℝ → ℝ) (h0 : g 0 = 0) (h1 : g h = 0)
    (hc : g h - g 0 = -c) : c = 0 := by
  rw [h0, h1] at hc
  linarith
lemma bounded_profile_cut (h c : ℝ) : boundedTemporalProfile h c 0 = 0 := by
  simp [boundedTemporalProfile]
lemma bounded_profile_value (h c : ℝ) (hh : h ≠ 0) : boundedTemporalProfile h c h = c := by
  unfold boundedTemporalProfile
  have hp : 1 + h ^ 2 ≠ 0 := by positivity
  field_simp
lemma bounded_profile_derivative (h c : ℝ) :
    HasDerivAt (boundedTemporalProfile h c) 0 0 := by
  have hd := (((hasDerivAt_id (0 : ℝ)).pow 2).div
    ((hasDerivAt_const (0 : ℝ) 1).add ((hasDerivAt_id (0 : ℝ)).pow 2)) (by norm_num)).const_mul
    (c * ((1 + h ^ 2) / h ^ 2))
  convert hd using 1 <;> simp
  all_goals rfl
lemma bounded_profile_bound (h c t : ℝ) :
    |boundedTemporalProfile h c t| ≤ |c * ((1 + h ^ 2) / h ^ 2)| := by
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hs : 0 ≤ t ^ 2 / (1 + t ^ 2) := by positivity
  have hb : t ^ 2 / (1 + t ^ 2) ≤ 1 := (div_le_one hp).mpr (by linarith)
  unfold boundedTemporalProfile
  rw [abs_mul, abs_of_nonneg hs]
  exact mul_le_of_le_one_right (abs_nonneg _) hb
lemma bounded_N4_profile_bound (h a t : ℝ) (hh : 0 < h) :
    |boundedTemporalProfile h (h ^ 3 * a / 4) t| ≤ h * |a| * (1 + h ^ 2) / 4 := by
  have hb := bounded_profile_bound h (h ^ 3 * a / 4) t
  have he : h ^ 3 * a / 4 * ((1 + h ^ 2) / h ^ 2) = h * a * (1 + h ^ 2) / 4 := by
    field_simp
  rw [he] at hb
  simpa [abs_mul, abs_div, abs_of_pos hh, abs_of_nonneg (show 0 ≤ 1 + h ^ 2 by positivity)] using hb
/-- **GAC2:higher-temporal-profile-budget**
(higher temporal lorentz jets with explicit real profile bounds). -/
@[ledger "GAC2:higher-temporal-profile-budget"]
theorem temporalProfileLaw : Statement.temporalProfileLaw := by
  exact ⟨temporal_profile_cut,
    temporal_profile_value,
    temporal_profile_derivative,
    temporal_log_adjustment,
    temporal_physical_adjustment,
    leading_scaled_profile,
    no_forward_frame_preserving_adjustment,
    bounded_profile_cut,
    bounded_profile_value,
    bounded_profile_derivative,
    bounded_profile_bound,
    bounded_N4_profile_bound⟩
/-! ## Non-vacuity -/
example : boundedTemporalProfile 1 1 0 = 0 ∧ boundedTemporalProfile 1 1 1 = 1 ∧
    HasDerivAt (boundedTemporalProfile 1 1) 0 0 := by
  exact ⟨bounded_profile_cut 1 1, bounded_profile_value 1 1 (by norm_num),
    bounded_profile_derivative 1 1⟩
end Artform.Scores.GravityBridge.Native.Full40
