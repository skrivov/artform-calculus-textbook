import ArtformScores.GravityBridge.Native.R8Angular

/-! # A scoped local differential inverse obstruction on a native radial subband -/

namespace Artform.Scores.GravityBridge.Native.R8

open Finset

open Polynomial Set

lemma no_polynomial_inverse_on_interval (c a b : ℝ) (P : Polynomial ℝ) (hab : a < b) :
    ¬ ∀ t ∈ Set.Ioo a b, c * t ^ 4 * P.eval t = 1 := by
  intro h
  have he : C c * X ^ 4 * P = (1 : Polynomial ℝ) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Ioo_infinite hab).mono
    intro t ht
    simpa only [Set.mem_ofPred_eq, eval_mul, eval_C, eval_pow, eval_X, eval_one] using h t ht
  have h0 := congrArg (Polynomial.eval (0 : ℝ)) he
  norm_num at h0

lemma no_complex_polynomial_inverse_on_interval (c : ℂ) (a b : ℝ) (P : Polynomial ℂ) (hab : a < b) :
    ¬ ∀ t ∈ Set.Ioo a b, c * (t : ℂ) ^ 4 * P.eval (t : ℂ) = 1 := by
  intro h
  have hi : Set.Infinite (Complex.ofReal '' Set.Ioo a b) :=
    (Set.Ioo_infinite hab).image Complex.ofReal_injective.injOn
  have he : C c * X ^ 4 * P = (1 : Polynomial ℂ) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hi.mono
    rintro z ⟨t, ht, rfl⟩
    simpa only [Set.mem_ofPred_eq, eval_mul, eval_C, eval_pow, eval_X, eval_one] using h t ht
  have h0 := congrArg (Polynomial.eval (0 : ℂ)) he
  norm_num at h0

lemma native_no_polynomial_inverse (P : Polynomial ℂ) :
    ¬ ∀ t ∈ Set.Ioo (1 : ℝ) 2,
      (leadingScalar (fun i => t * (![1, 2, 3] : Fin 3 → ℝ) i) : ℂ) * P.eval (t : ℂ) = 1 := by
  intro h
  apply no_complex_polynomial_inverse_on_interval (leadingScalar ![1, 2, 3] : ℂ) 1 2 P (by norm_num)
  intro t ht
  have he := h t ht
  rw [leading_scalar_homogeneous] at he
  push_cast at he
  linear_combination he

/-- **GAC:r8-leading-local-inverse** (polynomial symbols cannot invert this leading scalar). -/
@[ledger "GAC:r8-leading-local-inverse"]
theorem leadingLocalInverse : Statement.leadingLocalInverse :=
  ⟨no_polynomial_inverse_on_interval, no_complex_polynomial_inverse_on_interval,
    native_no_polynomial_inverse⟩

/-! ## Non-vacuity -/

example : (3 / 2 : ℝ) ∈ Set.Ioo (1 : ℝ) 2 ∧ leadingScalar ![1, 2, 3] ≠ 0 := by
  exact ⟨by norm_num, (leading_scalar_inverse _ 1 (by norm_num [radialSq,
    Fin.sum_univ_succ]) (by norm_num) separated_123).1⟩

end Artform.Scores.GravityBridge.Native.R8
