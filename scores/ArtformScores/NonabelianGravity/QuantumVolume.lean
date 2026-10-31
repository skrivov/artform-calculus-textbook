import ArtformScores.NonabelianGravity.HistoryReference
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Transport one declared native Lebesgue volume through real congruences -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.QuantumComposition
open HistoryElimination HistoryGaussian MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma determinant_congruence (H T : Matrix ι ι ℚ) (d : ι → ℚ)
    (hc : T.transpose * H * T = Matrix.diagonal d) :
    T.det ^ 2 * H.det = ∏ i, d i := by
  have h := congrArg Matrix.det hc
  simpa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, pow_two,
    mul_comm, mul_left_comm, mul_assoc] using h

noncomputable def certificateOfNonzero (H T : Matrix ι ι ℚ) (d : ι → ℚ)
    (hc : T.transpose * H * T = Matrix.diagonal d) (hd : ∀ i, d i ≠ 0) : Certificate H := by
  have hp : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  have ht : T.det ≠ 0 := by
    intro hz
    rw [← determinant_congruence H T d hc, hz] at hp
    simp at hp
  exact ⟨T, T⁻¹, d, Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr ht),
    Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr ht), hc⟩

noncomputable def activeEquiv {H : Matrix ι ι ℚ} (c : Certificate H)
    (hd : ∀ i, c.diagonal i ≠ 0) : Active c ≃ ι where
  toFun := Subtype.val
  invFun i := ⟨i, hd i⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma source_contact_equal {H : Matrix ι ι ℚ} (c₁ c₂ : Certificate H)
    (hd₁ : ∀ i, c₁.diagonal i ≠ 0) (hd₂ : ∀ i, c₂.diagonal i ≠ 0) (r : ι → ℚ) :
    sourceContact c₁ r = sourceContact c₂ r := by
  have hc₁ : Compatible c₁ r := fun i hi => False.elim (hd₁ i hi)
  have hc₂ : Compatible c₂ r := fun i hi => False.elim (hd₂ i hi)
  have hs₁ := solution_valid c₁ r 0 hc₁
  have he := solution_complete c₂ (solution c₁ r 0) r hs₁
  have hfree : solution c₂ r (c₂.backward.mulVec (solution c₁ r 0)) = solution c₂ r 0 := by
    unfold solution
    congr 1
    funext i
    simp only [hd₂ i, ite_false]
  rw [hfree] at he
  have h₁ := stationary_quadratic c₁ r 0 hc₁
  have h₂ := stationary_quadratic c₂ r 0 hc₂
  rw [← he] at h₂
  linarith

noncomputable def realJacobian {H : Matrix ι ι ℚ} (c : Certificate H) : ℝ :=
  |(c.forward.det : ℝ)|

lemma native_volume_transport {H : Matrix ι ι ℚ} (c : Certificate H) :
    Measure.map (Matrix.toLin' (c.forward.map (algebraMap ℚ ℝ))) volume =
      ENNReal.ofReal ((realJacobian c)⁻¹) • (volume : Measure (ι → ℝ)) := by
  have hdet : c.forward.det ≠ 0 := by
    have h := congrArg Matrix.det c.left_inverse
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact right_ne_zero_of_mul_eq_one h
  have he : (c.forward.map (algebraMap ℚ ℝ)).det = (c.forward.det : ℝ) :=
    (Rat.cast_det c.forward).symm
  have hreal : (c.forward.map (algebraMap ℚ ℝ)).det ≠ 0 := by
    rw [he]
    exact_mod_cast hdet
  simpa [realJacobian, he, abs_inv] using
    Real.map_matrix_volume_pi_eq_smul_volume_pi hreal

noncomputable def magnitude (d : ι → ℝ) (ℏ : ℝ) : ℝ :=
  ∏ i, Real.sqrt (Real.pi / (|d i| / (2 * ℏ)))

omit [DecidableEq ι] in
lemma magnitude_nonnegative (d : ι → ℝ) (ℏ : ℝ) : 0 ≤ magnitude d ℏ :=
  Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)

omit [DecidableEq ι] in
lemma magnitude_square (d : ι → ℝ) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    magnitude d ℏ ^ 2 = (2 * Real.pi * ℏ) ^ Fintype.card ι / ∏ i, |d i| := by
  unfold magnitude
  rw [← Finset.prod_pow]
  have he (i : ι) : Real.sqrt (Real.pi / (|d i| / (2 * ℏ))) ^ 2 =
      (2 * Real.pi * ℏ) / |d i| := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  simp_rw [he]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

lemma jacobian_diagonal {H : Matrix ι ι ℚ} (c : Certificate H) :
    realJacobian c ^ 2 * |(H.det : ℝ)| = ∏ i, |(c.diagonal i : ℝ)| := by
  have h := determinant_congruence H c.forward c.diagonal c.congruence
  have hr : (c.forward.det : ℝ) ^ 2 * (H.det : ℝ) = ∏ i, (c.diagonal i : ℝ) := by
    exact_mod_cast h
  have hh := congrArg abs hr
  simpa [realJacobian, abs_mul, abs_pow, Finset.abs_prod] using hh

lemma normalized_magnitude {H : Matrix ι ι ℚ} (c₁ c₂ : Certificate H)
    (hd₁ : ∀ i, c₁.diagonal i ≠ 0) (hd₂ : ∀ i, c₂.diagonal i ≠ 0)
    (ℏ : ℝ) (hℏ : 0 < ℏ) :
    realJacobian c₁ * magnitude (fun i => (c₁.diagonal i : ℝ)) ℏ =
      realJacobian c₂ * magnitude (fun i => (c₂.diagonal i : ℝ)) ℏ := by
  have hp₁ : (∏ i, |(c₁.diagonal i : ℝ)|) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => abs_ne_zero.mpr (by exact_mod_cast hd₁ i))
  have hp₂ : (∏ i, |(c₂.diagonal i : ℝ)|) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => abs_ne_zero.mpr (by exact_mod_cast hd₂ i))
  have hJ₁ := jacobian_diagonal c₁
  have hJ₂ := jacobian_diagonal c₂
  have hH : |(H.det : ℝ)| ≠ 0 := by intro hz; rw [hz, mul_zero] at hJ₁; exact hp₁ hJ₁.symm
  have hs : (realJacobian c₁ * magnitude (fun i => (c₁.diagonal i : ℝ)) ℏ) ^ 2 =
      (realJacobian c₂ * magnitude (fun i => (c₂.diagonal i : ℝ)) ℏ) ^ 2 := by
    rw [mul_pow, mul_pow, magnitude_square _ ℏ hℏ, magnitude_square _ ℏ hℏ,
      ← hJ₁, ← hJ₂]
    have hj₁ : realJacobian c₁ ≠ 0 := by intro hz; rw [hz] at hJ₁; simp at hJ₁; exact hp₁ hJ₁.symm
    have hj₂ : realJacobian c₂ ≠ 0 := by intro hz; rw [hz] at hJ₂; simp at hJ₂; exact hp₂ hJ₂.symm
    field_simp
  have hn₁ := mul_nonneg (abs_nonneg (c₁.forward.det : ℝ))
    (magnitude_nonnegative (fun i => (c₁.diagonal i : ℝ)) ℏ)
  have hn₂ := mul_nonneg (abs_nonneg (c₂.forward.det : ℝ))
    (magnitude_nonnegative (fun i => (c₂.diagonal i : ℝ)) ℏ)
  dsimp [realJacobian] at hs ⊢
  nlinarith

noncomputable def volumeReference {H : Matrix ι ι ℚ} (c : Certificate H)
    (E : ℚ) (r : ι → ℚ) (ℏ : ℝ) : ℂ :=
  (realJacobian c : ℂ) * referenceAmplitude c E r ℏ

lemma common_volume_composition {H : Matrix ι ι ℚ} (c₁ c₂ : Certificate H)
    (hd₁ : ∀ i, c₁.diagonal i ≠ 0) (hd₂ : ∀ i, c₂.diagonal i ≠ 0)
    (hphase : rotationPhase c₁ = rotationPhase c₂)
    (E : ℚ) (r : ι → ℚ) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    volumeReference c₁ E r ℏ = volumeReference c₂ E r ℏ := by
  have hp (c : Certificate H) (hd : ∀ i, c.diagonal i ≠ 0) :
      (∏ i : Active c, Real.sqrt (Real.pi / (|activeDiagonal c i| / (2 * ℏ)))) =
        magnitude (fun i => (c.diagonal i : ℝ)) ℏ := by
    exact (activeEquiv c hd).prod_comp
      (fun i : ι => Real.sqrt (Real.pi / (|(c.diagonal i : ℝ)| / (2 * ℏ))))
  unfold volumeReference
  rw [reference_amplitude_formula c₁ E r ℏ hℏ, reference_amplitude_formula c₂ E r ℏ hℏ,
    hp c₁ hd₁, hp c₂ hd₂, hphase]
  have hS : stationary c₁ E r = stationary c₂ E r := by
    rw [stationary, stationary, source_contact_equal c₁ c₂ hd₁ hd₂ r]
  rw [hS]
  have hm := congrArg (fun x : ℝ => (x : ℂ)) (normalized_magnitude c₁ c₂ hd₁ hd₂ ℏ hℏ)
  push_cast at hm
  linear_combination (rotationPhase c₂ * Complex.exp
    (Complex.I * (stationary c₂ E r : ℂ) / ℏ)) * hm

end Artform.Scores.NonabelianGravity.QuantumComposition
