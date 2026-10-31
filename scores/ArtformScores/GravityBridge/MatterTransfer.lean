import ArtformScores.GravityBridge.MatterTransferStatements
/-! # Clock backreaction and the finite Gaussian domain -/
namespace Artform.Scores.GravityBridge
noncomputable section
open MeasureTheory
lemma nonzero_clock_not_lapse_stationary (coupling : ℝ) (hc : coupling ≠ 0) :
    ¬ HasDerivAt (fun N : ℝ => coupling / (2 * N)) 0 1 := by
  intro h
  have he := (lapse_density_derivative coupling).unique h
  apply hc
  linarith
lemma compensated_clock_lapse (coupling c : ℝ) :
    HasDerivAt (fun N : ℝ => coupling / (2 * N) + c * (N - 1)) (c - coupling / 2) 1 := by
  have h : HasDerivAt (fun N : ℝ => coupling / (2 * N) + c * (N - 1))
      (-coupling / 2 + (0 * (1 - 1) + c * 1)) 1 :=
    (lapse_density_derivative coupling).add
      ((hasDerivAt_const (1 : ℝ) c).mul ((hasDerivAt_id 1).sub_const 1))
  convert h using 1
  ring
lemma clock_lapse_cancellation (coupling c : ℝ) :
    HasDerivAt (fun N : ℝ => coupling / (2 * N) + c * (N - 1)) 0 1 ↔ c = coupling / 2 := by
  constructor
  · intro h
    have he := (compensated_clock_lapse coupling c).unique h
    linarith
  · intro h
    have hd := compensated_clock_lapse coupling c
    simpa [h] using hd
lemma outside_window_not_integrable : ¬ Integrable (loopGaussianBlock 1 1 2) := by
  intro hf
  change Integrable (loopGaussianBlock 1 1 2) (volume.prod volume) at hf
  have hi := hf.integral_prod_left
  have hinner (q : ℝ) : (∫ z : ℝ, loopGaussianBlock 1 1 2 (q, z)) =
      Real.exp (-(-3 / 2 : ℝ) * q ^ 2) * Real.sqrt (2 * Real.pi) := by
    have he : (fun z : ℝ => loopGaussianBlock 1 1 2 (q, z)) =
        fun z : ℝ => Real.exp (-gaussianAction (1 / 2) 1 (1 / 2) 0 0 q z) := by
      funext z
      dsimp [loopGaussianBlock, gaussianAction]
      congr 1
      ring
    rw [he, (gaussian_schur_integral (1 / 2) 1 (1 / 2) 0 0 q (by norm_num)).2]
    congr 1
    · dsimp [gaussianEffective]
      congr 1
      ring
    · congr 1
      ring
  have he : (fun q : ℝ => ∫ z : ℝ, loopGaussianBlock 1 1 2 (q, z)) =
      fun q : ℝ => Real.exp (-(-3 / 2 : ℝ) * q ^ 2) * Real.sqrt (2 * Real.pi) :=
    funext hinner
  rw [he] at hi
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hb : Integrable (fun q : ℝ => Real.exp (-(-3 / 2 : ℝ) * q ^ 2)) := by
    convert hi.div_const (Real.sqrt (2 * Real.pi)) using 1
    funext q
    exact (mul_div_cancel_right₀ _ hs).symm
  rw [integrable_exp_neg_mul_sq_iff] at hb
  norm_num at hb
/-- **GAC:matter-transfer-obligations** (clock backreaction and the finite gaussian domain). -/
@[ledger "GAC:matter-transfer-obligations"]
theorem matterTransferLaw : Statement.matterTransferLaw := by
  exact ⟨nonzero_clock_not_lapse_stationary,
    compensated_clock_lapse,
    clock_lapse_cancellation,
    outside_window_not_integrable⟩
/-! ## Non-vacuity -/
example : HasDerivAt (fun N : ℝ => 7 / (2 * N) + (7 / 2) * (N - 1)) 0 1 ∧
    ¬ HasDerivAt (fun N : ℝ => 7 / (2 * N)) 0 1 :=
  ⟨(clock_lapse_cancellation 7 (7 / 2)).mpr rfl,
    nonzero_clock_not_lapse_stationary 7 (by norm_num)⟩
end
end Artform.Scores.GravityBridge
