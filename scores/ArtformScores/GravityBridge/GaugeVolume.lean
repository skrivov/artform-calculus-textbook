import ArtformScores.GravityBridge.GaugeVolumeStatements

/-! # Slice convergence does not remove the unfixed gauge volume -/

namespace Artform.Scores.GravityBridge

noncomputable section

open MeasureTheory

lemma gauge_gaussian_factor (epsilon : ℝ) (x : ℝ × ℝ) :
    gaugeGaussian epsilon x = Real.exp (-x.1 ^ 2) * Real.exp (-epsilon * x.2 ^ 2) := by
  rw [gaugeGaussian, ← Real.exp_add]
  congr 1
  ring

lemma unfixed_gauge_not_integrable : ¬ Integrable (gaugeGaussian 0) := by
  intro h
  have hs : ∀ᵐ q : ℝ, Integrable (fun g : ℝ => gaugeGaussian 0 (q, g)) :=
    h.prod_right_ae
  obtain ⟨q, hq⟩ := hs.exists
  have he : (fun g : ℝ => gaugeGaussian 0 (q, g)) =
      (fun _ : ℝ => Real.exp (-q ^ 2)) := by funext g; simp [gaugeGaussian]
  rw [he, integrable_const_iff] at hq
  rcases hq with hz | hf
  · exact Real.exp_ne_zero _ hz
  · have hv : (volume : Measure ℝ) Set.univ = ⊤ := by simp
    have hn := hf.measure_univ_lt_top
    rw [hv] at hn
    exact (lt_irrefl _) hn

lemma fixed_gauge_slice : Integrable (fun q : ℝ => gaugeGaussian 0 (q, 0)) ∧
    (∫ q : ℝ, gaugeGaussian 0 (q, 0)) = Real.sqrt Real.pi := by
  constructor
  · simpa [gaugeGaussian] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  · simpa [gaugeGaussian] using integral_gaussian (1 : ℝ)

lemma regulated_gauge_integral (epsilon : ℝ) (he : 0 < epsilon) :
    Integrable (gaugeGaussian epsilon) ∧
    (∫ x : ℝ × ℝ, gaugeGaussian epsilon x) =
      Real.sqrt Real.pi * Real.sqrt (Real.pi / epsilon) := by
  have hq := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hg := integrable_exp_neg_mul_sq he
  have hf : (gaugeGaussian epsilon) = fun x : ℝ × ℝ =>
      Real.exp (-1 * x.1 ^ 2) * Real.exp (-epsilon * x.2 ^ 2) := by
    funext x
    simpa using gauge_gaussian_factor epsilon x
  rw [hf]
  constructor
  · exact hq.mul_prod hg
  · change (∫ x : ℝ × ℝ, Real.exp (-1 * x.1 ^ 2) *
        Real.exp (-epsilon * x.2 ^ 2) ∂volume.prod volume) = _
    rw [integral_prod_mul (fun q : ℝ => Real.exp (-1 * q ^ 2))
      (fun g : ℝ => Real.exp (-epsilon * g ^ 2)),
      integral_gaussian, integral_gaussian]
    simp

lemma regulator_changes_amplitude :
    (∫ x : ℝ × ℝ, gaugeGaussian 1 x) = Real.pi ∧
    (∫ x : ℝ × ℝ, gaugeGaussian 4 x) = Real.pi / 2 ∧
    (∫ x : ℝ × ℝ, gaugeGaussian 1 x) ≠ (∫ x : ℝ × ℝ, gaugeGaussian 4 x) := by
  have h1 := (regulated_gauge_integral 1 (by norm_num)).2
  have h4 := (regulated_gauge_integral 4 (by norm_num)).2
  have hs : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  simp only [div_one] at h1
  rw [hs] at h1
  rw [Real.sqrt_div Real.pi_pos.le, show Real.sqrt (4 : ℝ) = 2 by norm_num] at h4
  have h4' : (∫ x : ℝ × ℝ, gaugeGaussian 4 x) = Real.pi / 2 := by
    rw [h4]
    nlinarith
  refine ⟨h1, h4', ?_⟩
  rw [h1, h4']
  linarith [Real.pi_pos]

/-- **GAC:gaussian-gauge-volume** (a real singular model, not a native gauge fixing). -/
@[ledger "GAC:gaussian-gauge-volume"]
theorem gaugeVolumeLaw : Statement.gaugeVolumeLaw := by
  exact ⟨unfixed_gauge_not_integrable, fixed_gauge_slice,
    regulated_gauge_integral, regulator_changes_amplitude⟩

/-! ## Non-vacuity -/

example : Integrable (gaugeGaussian 1) ∧ ¬ Integrable (gaugeGaussian 0) :=
  ⟨(regulated_gauge_integral 1 (by norm_num)).1, unfixed_gauge_not_integrable⟩

end

end Artform.Scores.GravityBridge
