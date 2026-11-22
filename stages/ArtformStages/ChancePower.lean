import ArtformStages.TheWalk

/-!
# Only the square

Among the rules of chance that are powers of the sizes of a wave's numbers, the link gate of
`TheWalk.lean` keeps only the square (finding 479 of the research ledger on a layered universe):

* `gate_power_iff` (CH1): for every real `q > 0`, the link gate at an eighth of a turn,
  `coin (π / 4)`, keeps the sum of the `q`-th powers of the sizes of every two complex numbers
  exactly when `q = 2`.

The gate keeps the sum of the squares by `exchange_unitary_iff`. It takes the numbers `(1, 0)` to
`(1/√2, -i/√2)`, so it moves the sum of their `q`-th powers from `1` to `2 (1/√2)^q`, which is `1`
only for `q = 2`.
-/

open Matrix Complex
open scoped Real

namespace Artform.Stages

/-- **CH1.** Only the square: for every real `q > 0`, the link gate at an eighth of a turn keeps
the sum of the `q`-th powers of the sizes of every two complex numbers exactly when `q = 2`. -/
theorem gate_power_iff (q : ℝ) (hq : 0 < q) :
    (∀ v : Fin 2 → ℂ, ∑ i, ‖(coin (π / 4) *ᵥ v) i‖ ^ q = ∑ i, ‖v i‖ ^ q) ↔ q = 2 := by
  have hcoin : ∀ v : Fin 2 → ℂ, ∑ i, ‖(coin (π / 4) *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
    intro v
    have e : coin (π / 4) = (Real.cos (π / 4) : ℂ) • 1 + (-(I * Real.sin (π / 4))) • pauliX := by
      rw [coin, neg_smul, sub_eq_add_neg]
    rw [e]
    refine ((exchange_unitary_iff _ _).2.mpr ⟨1, -(π / 4), by simp, ?_, ?_⟩) v
    · simp [Real.cos_neg]
    · simp [Real.sin_neg]
  constructor
  · intro h
    have e := h ![1, 0]
    have h0 : (coin (π / 4) *ᵥ ![1, 0]) 0 = (Real.cos (π / 4) : ℂ) := by
      simp [coin, pauliX, mulVec, dotProduct, Fin.sum_univ_two]
    have h1 : (coin (π / 4) *ᵥ ![1, 0]) 1 = -(I * Real.sin (π / 4)) := by
      simp [coin, pauliX, mulVec, dotProduct, Fin.sum_univ_two]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, h0, h1] at e
    have hx : 0 < √2 / 2 := by positivity
    have hn0 : ‖(Real.cos (π / 4) : ℂ)‖ = √2 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, Real.cos_pi_div_four, abs_of_pos hx]
    have hn1 : ‖-(I * (Real.sin (π / 4) : ℂ))‖ = √2 / 2 := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        Real.sin_pi_div_four, abs_of_pos hx]
    rw [hn0, hn1] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_one,
      norm_zero, Real.one_rpow, Real.zero_rpow hq.ne', add_zero] at e
    have hsq : (√2 / 2) ^ (2 : ℝ) = 1 / 2 := by
      rw [Real.rpow_two, div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hhalf : (√2 / 2) ^ q = (√2 / 2) ^ (2 : ℝ) := by
      rw [hsq]
      linarith
    have hne : √2 / 2 ≠ 1 := by
      intro h1
      have h2 : (√2 / 2) ^ (2 : ℝ) = 1 := by rw [h1, Real.one_rpow]
      rw [hsq] at h2
      norm_num at h2
    exact (Real.rpow_right_inj hx hne).mp hhalf
  · rintro rfl v
    simp only [Real.rpow_two]
    exact hcoin v

end Artform.Stages
