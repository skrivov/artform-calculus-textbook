import ArtformScores.GravityBridge.LoopStatements

/-! # The declared Gaussian loop has a certified finite response and remainder -/

namespace Artform.Scores.GravityBridge

noncomputable section

open MeasureTheory

lemma loop_block_integral (A B s : ℝ) (hB : 0 < B) (hd : 0 < A * B - s ^ 2) :
    Integrable (loopGaussianBlock A B s) ∧
    (∫ x : ℝ × ℝ, loopGaussianBlock A B s x) =
      Real.sqrt (Real.pi / loopSchur A B s) * Real.sqrt (Real.pi / (B / 2)) := by
  have hB2 : 0 < B / 2 := by linarith
  have hc : 0 < loopSchur A B s := by
    have he : loopSchur A B s = (A * B - s ^ 2) / (2 * B) := by
      dsimp [loopSchur]
      field_simp
    rw [he]
    positivity
  have he (q : ℝ) : (fun z : ℝ => loopGaussianBlock A B s (q, z)) =
      (fun z : ℝ => Real.exp (-gaussianAction (B / 2) (s / 2) (A / 2) 0 0 q z)) := by
    funext z
    dsimp [loopGaussianBlock, gaussianAction]
    congr 1
    ring
  have hi (q : ℝ) := gaussian_schur_integral (B / 2) (s / 2) (A / 2) 0 0 q hB2
  have hinner (q : ℝ) : (∫ z : ℝ, loopGaussianBlock A B s (q, z)) =
      Real.exp (-loopSchur A B s * q ^ 2) * Real.sqrt (Real.pi / (B / 2)) := by
    rw [he q, (hi q).2]
    congr 2
    dsimp [gaussianEffective, loopSchur]
    ring
  have hm : AEStronglyMeasurable (loopGaussianBlock A B s)
      ((volume : Measure ℝ).prod volume) := by
    have hcont : Continuous (loopGaussianBlock A B s) := by
      change Continuous (fun x : ℝ × ℝ =>
        Real.exp (-(A * x.1 ^ 2 + 2 * s * x.1 * x.2 + B * x.2 ^ 2) / 2))
      fun_prop
    exact hcont.aestronglyMeasurable
  have hnorm (x : ℝ × ℝ) : ‖loopGaussianBlock A B s x‖ = loopGaussianBlock A B s x := by
    change |Real.exp _| = Real.exp _
    exact abs_of_pos (Real.exp_pos _)
  have hf : Integrable (loopGaussianBlock A B s) := by
    change Integrable (loopGaussianBlock A B s) (volume.prod volume)
    rw [integrable_prod_iff hm]
    constructor
    · exact Filter.Eventually.of_forall (fun q => by rw [he q]; exact (hi q).1)
    · have hn : (fun q : ℝ => ∫ z : ℝ, ‖loopGaussianBlock A B s (q, z)‖) =
          fun q : ℝ => Real.exp (-loopSchur A B s * q ^ 2) *
            Real.sqrt (Real.pi / (B / 2)) := by
        funext q
        simp_rw [hnorm]
        exact hinner q
      rw [hn]
      exact (integrable_exp_neg_mul_sq hc).mul_const _
  refine ⟨hf, ?_⟩
  change (∫ x : ℝ × ℝ, loopGaussianBlock A B s x ∂volume.prod volume) = _
  rw [integral_prod _ hf]
  simp_rw [hinner]
  rw [integral_mul_const, integral_gaussian]

lemma loop_schur_positive (A B s : ℝ) (hB : 0 < B) (hd : 0 < A * B - s ^ 2) :
    0 < loopSchur A B s := by
  have he : loopSchur A B s = (A * B - s ^ 2) / (2 * B) := by
    dsimp [loopSchur]
    field_simp
  rw [he]
  positivity

lemma loop_block_log (A B s : ℝ) (hB : 0 < B) (hd : 0 < A * B - s ^ 2) :
    Real.log (∫ x : ℝ × ℝ, loopGaussianBlock A B s x) =
      Real.log Real.pi - (Real.log (loopSchur A B s) + Real.log (B / 2)) / 2 := by
  have hc := loop_schur_positive A B s hB hd
  have hB2 : 0 < B / 2 := by linarith
  have hp0 : 0 < Real.pi / loopSchur A B s := div_pos Real.pi_pos hc
  have hp1 : 0 < Real.pi / (B / 2) := div_pos Real.pi_pos hB2
  rw [(loop_block_integral A B s hB hd).2,
    Real.log_mul (ne_of_gt (Real.sqrt_pos.2 hp0)) (ne_of_gt (Real.sqrt_pos.2 hp1)),
    Real.log_sqrt hp0.le, Real.log_sqrt hp1.le,
    Real.log_div Real.pi_ne_zero (ne_of_gt hc),
    Real.log_div Real.pi_ne_zero (ne_of_gt hB2)]
  ring

lemma loop_block_log_ratio (A B s : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hd : 0 < A * B - s ^ 2) :
    Real.log ((∫ x : ℝ × ℝ, loopGaussianBlock A B s x) /
      (∫ x : ℝ × ℝ, loopGaussianBlock A B 0 x)) =
      -(1 / 2) * Real.log (1 - s ^ 2 / (A * B)) := by
  have h0 : 0 < A * B - (0 : ℝ) ^ 2 := by simpa using mul_pos hA hB
  have hz (t : ℝ) (ht : 0 < A * B - t ^ 2) :
      0 < ∫ x : ℝ × ℝ, loopGaussianBlock A B t x := by
    rw [(loop_block_integral A B t hB ht).2]
    exact mul_pos (Real.sqrt_pos.2 (div_pos Real.pi_pos
      (loop_schur_positive A B t hB ht)))
      (Real.sqrt_pos.2 (div_pos Real.pi_pos (by linarith)))
  rw [Real.log_div (ne_of_gt (hz s hd)) (ne_of_gt (hz 0 h0)),
    loop_block_log A B s hB hd, loop_block_log A B 0 hB h0]
  have he : loopSchur A B s / (A / 2) = 1 - s ^ 2 / (A * B) := by
    dsimp [loopSchur]
    field_simp
  have hl := Real.log_div (ne_of_gt (loop_schur_positive A B s hB hd))
    (ne_of_gt (show 0 < A / 2 by linarith))
  rw [he] at hl
  simp only [loopSchur, zero_div, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] at *
  linarith

lemma loop_block_integral_pos (A B s : ℝ) (hB : 0 < B) (hd : 0 < A * B - s ^ 2) :
    0 < ∫ x : ℝ × ℝ, loopGaussianBlock A B s x := by
  rw [(loop_block_integral A B s hB hd).2]
  exact mul_pos (Real.sqrt_pos.2 (div_pos Real.pi_pos
    (loop_schur_positive A B s hB hd)))
    (Real.sqrt_pos.2 (div_pos Real.pi_pos (by linarith)))

lemma finite_loop_partition {I : Type*} [Fintype I] (A B : I → ℝ) (s : ℝ)
    (hB : ∀ i, 0 < B i) (hd : ∀ i, 0 < A i * B i - s ^ 2) :
    Integrable (fun x : I → ℝ × ℝ => ∏ i, loopGaussianBlock (A i) (B i) s (x i)) ∧
    finiteLoopPartition A B s =
      ∏ i, (Real.sqrt (Real.pi / loopSchur (A i) (B i) s) * Real.sqrt (Real.pi / (B i / 2))) := by
  constructor
  · change Integrable _ (Measure.pi (fun _ : I => (volume : Measure (ℝ × ℝ))))
    exact Integrable.fintype_prod_dep (fun i => (loop_block_integral _ _ _ (hB i) (hd i)).1)
  · unfold finiteLoopPartition
    rw [integral_fintype_prod_volume_eq_prod]
    congr 1
    ext i
    exact (loop_block_integral _ _ _ (hB i) (hd i)).2

lemma finite_loop_log_ratio {I : Type*} [Fintype I] (A B : I → ℝ) (s : ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hd : ∀ i, 0 < A i * B i - s ^ 2) :
    Real.log (finiteLoopPartition A B s / finiteLoopPartition A B 0) =
      -(1 / 2) * ∑ i, Real.log (1 - s ^ 2 / (A i * B i)) := by
  have h0 (i : I) : 0 < A i * B i - (0 : ℝ) ^ 2 := by simpa using mul_pos (hA i) (hB i)
  have hzs (i : I) : (∫ x : ℝ × ℝ, loopGaussianBlock (A i) (B i) s x) ≠ 0 :=
    ne_of_gt (loop_block_integral_pos _ _ _ (hB i) (hd i))
  have hz0 (i : I) : (∫ x : ℝ × ℝ, loopGaussianBlock (A i) (B i) 0 x) ≠ 0 :=
    ne_of_gt (loop_block_integral_pos _ _ _ (hB i) (h0 i))
  unfold finiteLoopPartition
  rw [integral_fintype_prod_volume_eq_prod, integral_fintype_prod_volume_eq_prod]
  rw [Real.log_div (Finset.prod_ne_zero_iff.mpr (fun i _ => hzs i))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hz0 i)),
    Real.log_prod (fun i _ => hzs i), Real.log_prod (fun i _ => hz0 i),
    ← Finset.sum_sub_distrib]
  have he (i : I) :
      Real.log (∫ x : ℝ × ℝ, loopGaussianBlock (A i) (B i) s x) -
        Real.log (∫ x : ℝ × ℝ, loopGaussianBlock (A i) (B i) 0 x) =
      -(1 / 2) * Real.log (1 - s ^ 2 / (A i * B i)) := by
    rw [← Real.log_div (hzs i) (hz0 i)]
    exact loop_block_log_ratio _ _ _ (hA i) (hB i) (hd i)
  simp_rw [he]
  rw [Finset.mul_sum]

lemma logarithm_response_error (x : ℝ) (h1 : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hy : 0 < 1 - x := by linarith
  have hu := Real.log_le_sub_one_of_pos hy
  have hl := Real.one_sub_inv_le_log_of_pos hy
  have hm : -x ≤ (1 - x) * Real.log (1 - x) := by
    calc
      -x = (1 - x) * (1 - (1 - x)⁻¹) := by field_simp; ring
      _ ≤ (1 - x) * Real.log (1 - x) := mul_le_mul_of_nonneg_left hl hy.le
  have hr : 0 ≤ -(Real.log (1 - x) + x) := by linarith
  rw [abs_of_nonpos (by linarith)]
  nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - x by linarith) hr]

lemma finite_loop_error {I : Type*} [Fintype I] (w : I → ℝ) (hw : ∀ i, 1 ≤ w i)
    (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1 / 2) :
    |finiteLoopFreeEnergy w theta + theta / 2 * ∑ i, 1 / w i| ≤
      Fintype.card I * theta ^ 2 := by
  have hi (i : I) : |Real.log (1 - theta / w i) + theta / w i| ≤ 2 * theta ^ 2 := by
    have hp : 0 < w i := by linarith [hw i]
    have hx0 : 0 ≤ theta / w i := div_nonneg h0 hp.le
    have hx1 : theta / w i ≤ theta := (div_le_self h0 (hw i))
    have hx2 : (theta / w i) ^ 2 ≤ theta ^ 2 := pow_le_pow_left₀ hx0 hx1 2
    exact (logarithm_response_error _ (hx1.trans h1)).trans (by nlinarith)
  have ht : (∑ i, theta / w i) = theta * ∑ i, 1 / w i := by
    simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
  have he : finiteLoopFreeEnergy w theta + theta / 2 * ∑ i, 1 / w i =
      (1 / 2 : ℝ) * ∑ i, (Real.log (1 - theta / w i) + theta / w i) := by
    unfold finiteLoopFreeEnergy
    rw [Finset.sum_add_distrib, ht]
    ring
  rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hs := Finset.abs_sum_le_sum_abs (fun i => Real.log (1 - theta / w i) + theta / w i)
    (Finset.univ : Finset I)
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  calc
    (1 / 2 : ℝ) * |∑ i, (Real.log (1 - theta / w i) + theta / w i)| ≤
        (1 / 2 : ℝ) * ∑ i, |Real.log (1 - theta / w i) + theta / w i| := by linarith
    _ ≤ (1 / 2 : ℝ) * ∑ _i : I, 2 * theta ^ 2 := by linarith
    _ = Fintype.card I * theta ^ 2 := by simp; ring

lemma regulator_pair_lower (i : Fin 4) (r : AxisRepresentatives i) :
    1 ≤ regulatorA i r ∧ 1 ≤ regulatorB i r ∧ (1 : ℝ) ≤ pairWeight i r := by
  have hA : 1 ≤ regulatorA i r := by
    dsimp [regulatorA]
    exact_mod_cast mode_precision_lower r.val
  have hB : 1 ≤ regulatorB i r := by
    dsimp [regulatorB]
    exact_mod_cast mode_precision_lower (r.val ^^^ momentumAxis i)
  refine ⟨hA, hB, ?_⟩
  change (1 : ℝ) ≤ (modePrecision 2 1 r.val *
    modePrecision 2 1 (r.val ^^^ momentumAxis i) : ℚ)
  push_cast
  dsimp [regulatorA, regulatorB] at hA hB
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]

lemma regulator_pair_product (i : Fin 4) (r : AxisRepresentatives i) :
    regulatorA i r * regulatorB i r = (pairWeight i r : ℝ) := by
  simp [regulatorA, regulatorB, pairWeight]

lemma regulator_free_energy (i : Fin 4) (s : ℝ) (hs : s ^ 2 ≤ 1 / 2) :
    regulatorFreeEnergy i s = finiteLoopFreeEnergy (fun r => (pairWeight i r : ℝ)) (s ^ 2) := by
  have hA (r : AxisRepresentatives i) : 0 < regulatorA i r := by
    linarith [(regulator_pair_lower i r).1]
  have hB (r : AxisRepresentatives i) : 0 < regulatorB i r := by
    linarith [(regulator_pair_lower i r).2.1]
  have hd (r : AxisRepresentatives i) :
      0 < regulatorA i r * regulatorB i r - s ^ 2 := by
    rw [regulator_pair_product]
    linarith [(regulator_pair_lower i r).2.2]
  unfold regulatorFreeEnergy
  rw [finite_loop_log_ratio _ _ s hA hB hd]
  simp_rw [regulator_pair_product]
  dsimp [finiteLoopFreeEnergy]
  ring

lemma regulator_loop_error (i : Fin 4) (s : ℝ) (hs : s ^ 2 ≤ 1 / 2) :
    |regulatorFreeEnergy i s - regulatorLoopCoefficient i * s ^ 2| ≤ 8 * s ^ 4 := by
  rw [regulator_free_energy i s hs]
  have he := finite_loop_error (fun r => (pairWeight i r : ℝ))
    (fun r => (regulator_pair_lower i r).2.2) (s ^ 2) (sq_nonneg s) hs
  have hsum : (∑ r : AxisRepresentatives i, 1 / (pairWeight i r : ℝ)) =
      (loopResponse 2 1 i : ℚ) / 2 := by exact_mod_cast pair_response_half i
  rw [hsum, axis_representative_card] at he
  have ht : s ^ 2 / 2 * (((loopResponse 2 1 i : ℚ) : ℝ) / 2) =
      -regulatorLoopCoefficient i * s ^ 2 := by
    dsimp [regulatorLoopCoefficient]
    ring
  have hp : (8 : ℝ) * (s ^ 2) ^ 2 = 8 * s ^ 4 := by ring
  norm_num only [Nat.cast_ofNat] at he
  rw [ht, hp] at he
  simpa only [sub_eq_add_neg, neg_mul] using he

lemma regulator_loop_gap :
    regulatorLoopCoefficient 0 = -19 / 40 ∧ regulatorLoopCoefficient 1 = -17 / 30 ∧
    regulatorLoopCoefficient 0 - regulatorLoopCoefficient 1 = 11 / 120 := by
  norm_num [regulatorLoopCoefficient, anisotropic_loop_response.1, anisotropic_loop_response.2]

/-- **GAC:finite-gaussian-loop** (an actual finite background partition and controlled response). -/
@[ledger "GAC:finite-gaussian-loop"]
theorem loopLaw : Statement.loopLaw := by
  refine ⟨loop_block_integral, loop_block_log_ratio, ?_, ?_, ?_,
    regulator_free_energy, regulator_loop_error, regulator_loop_gap⟩
  · intro I _ A B s hB hd
    exact finite_loop_partition A B s hB hd
  · intro I _ A B s hA hB hd
    exact finite_loop_log_ratio A B s hA hB hd
  · intro I _ w hw theta h0 h1
    exact finite_loop_error w hw theta h0 h1

/-! ## Non-vacuity -/

example : |regulatorFreeEnergy 0 (1 / 10) - (-19 / 40) * (1 / 10) ^ 2| ≤ 1 / 1250 := by
  have h := regulator_loop_error 0 (1 / 10) (by norm_num)
  rw [regulator_loop_gap.1] at h
  norm_num at h ⊢
  exact h

end

end Artform.Scores.GravityBridge
