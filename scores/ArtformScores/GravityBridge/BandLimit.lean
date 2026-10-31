import ArtformScores.GravityBridge.BandLimitStatements

/-! # The Gaussian limit is uniform on a fixed frequency band -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma gaussian_multiplier_error (h R : ℝ) (hh : 0 ≤ h) (hR : 0 ≤ R)
    (x : FrequencyBand R) : |gaussianMultiplier h R x - 1| ≤ h * R ^ 2 / 2 := by
  have hx : (x : ℝ) ^ 2 ≤ R ^ 2 := by
    apply sq_le_sq.mpr
    simpa [abs_of_nonneg hR] using (abs_le.mpr x.property)
  have hp : 0 ≤ h * (x : ℝ) ^ 2 / 2 := by positivity
  have he : Real.exp (-h * (x : ℝ) ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hl := Real.add_one_le_exp (-h * (x : ℝ) ^ 2 / 2)
  change |Real.exp (-h * (x : ℝ) ^ 2 / 2) - 1| ≤ _
  rw [abs_of_nonpos (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hx hh]

lemma gaussian_band_operator_error (h R : ℝ) (hh : 0 ≤ h) (hR : 0 ≤ R) :
    ‖gaussianBandStep h R - ContinuousLinearMap.id ℝ C(FrequencyBand R, ℝ)‖ ≤
      h * R ^ 2 / 2 := by
  have hm : ‖gaussianMultiplier h R - 1‖ ≤ h * R ^ 2 / 2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    exact gaussian_multiplier_error h R hh hR x
  have he : gaussianBandStep h R - ContinuousLinearMap.id ℝ C(FrequencyBand R, ℝ) =
      ContinuousLinearMap.mul ℝ _ (gaussianMultiplier h R - 1) := by
    ext f x
    simp [gaussianBandStep]
  rw [he]
  exact (ContinuousLinearMap.opNorm_mul_apply_le ℝ _ _).trans hm

lemma gaussian_band_norm_limit (R : ℝ) (hR : 0 ≤ R) :
    Filter.Tendsto
      (fun h : ℝ => ‖gaussianBandStep h R -
        ContinuousLinearMap.id ℝ C(FrequencyBand R, ℝ)‖)
      (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
  refine squeeze_zero' (f := fun h : ℝ => ‖gaussianBandStep h R -
    ContinuousLinearMap.id ℝ C(FrequencyBand R, ℝ)‖)
    (g := fun h : ℝ => h * R ^ 2 / 2) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun h => norm_nonneg (gaussianBandStep h R -
      ContinuousLinearMap.id ℝ C(FrequencyBand R, ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact gaussian_band_operator_error h R hh hR
  · have ht : Filter.Tendsto (fun h : ℝ => h * R ^ 2 / 2) (nhds 0) (nhds 0) := by
      simpa using (continuous_id.mul continuous_const |>.div_const (2 : ℝ)).tendsto (0 : ℝ)
    exact ht.mono_left nhdsWithin_le_nhds

lemma escaping_frequency (n : ℕ) :
    Real.exp (-(1 / ((n : ℝ) + 1)) * (Real.sqrt (2 * ((n : ℝ) + 1))) ^ 2 / 2) =
      Real.exp (-1) := by
  rw [Real.sq_sqrt (by positivity)]
  congr 1
  field_simp

lemma escaping_error_positive : 0 < |Real.exp (-1 : ℝ) - 1| := by
  have h : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt h))

lemma gaussian_step_sequence_limit :
    Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma escaping_error_not_tendsto :
    ¬ Filter.Tendsto (fun n : ℕ =>
      |Real.exp (-(1 / ((n : ℝ) + 1)) *
        (Real.sqrt (2 * ((n : ℝ) + 1))) ^ 2 / 2) - 1|)
      Filter.atTop (nhds 0) := by
  simp_rw [escaping_frequency]
  intro h
  have hz : |Real.exp (-1 : ℝ) - 1| = 0 :=
    tendsto_nhds_unique tendsto_const_nhds h
  exact (ne_of_gt escaping_error_positive) hz

/-- **GAC:gaussian-band-limit** (a fixed-space operator norm limit and escaping-frequency test). -/
@[ledger "GAC:gaussian-band-limit"]
theorem bandLimitLaw : Statement.bandLimitLaw := by
  exact ⟨gaussian_band_operator_error, gaussian_band_norm_limit, gaussian_step_sequence_limit,
    escaping_frequency, escaping_error_positive, escaping_error_not_tendsto⟩

/-! ## Non-vacuity -/

example : ‖gaussianBandStep (1 / 100) 2 -
    ContinuousLinearMap.id ℝ C(FrequencyBand 2, ℝ)‖ ≤ 1 / 50 := by
  convert gaussian_band_operator_error (1 / 100) 2 (by norm_num) (by norm_num) using 1
  norm_num

end

end Artform.Scores.GravityBridge
