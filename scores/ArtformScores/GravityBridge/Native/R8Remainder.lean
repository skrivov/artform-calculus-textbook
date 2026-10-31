import ArtformScores.GravityBridge.Native.R8Angular

/-! # An explicit finite-spacing budget with the native remainder still a hypothesis -/

namespace Artform.Scores.GravityBridge.Native.R8

open Finset

lemma perturbative_scalar_lower (k : Fin 3 → ℝ) (delta h M D : ℝ)
    (hk : 0 < radialSq k) (hd : 0 < delta) (hs : RaySeparated k delta)
    (hh : 0 < h) (_hM : 0 ≤ M)
    (hsmall : M * h ≤ radialSq k * delta ^ 2 / 174528)
    (herr : |D - h ^ 4 * leadingScalar k| ≤ M * h ^ 5) :
    h ^ 4 * radialSq k * delta ^ 2 / 174528 ≤ |D| := by
  have hl := leading_scalar_lower k delta hk hd hs
  have hp : |h ^ 4 * leadingScalar k| = h ^ 4 * |leadingScalar k| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have ht : |h ^ 4 * leadingScalar k| ≤ |D - h ^ 4 * leadingScalar k| + |D| := by
    have he : h ^ 4 * leadingScalar k = -(D - h ^ 4 * leadingScalar k) + D := by ring
    calc
      _ = |-(D - h ^ 4 * leadingScalar k) + D| := by rw [← he]
      _ ≤ |-(D - h ^ 4 * leadingScalar k)| + |D| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have h1 := mul_le_mul_of_nonneg_left hl (show 0 ≤ h ^ 4 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ h ^ 4 by positivity)
  rw [hp] at ht
  nlinarith

lemma perturbative_scalar_inverse (k : Fin 3 → ℝ) (delta h M D : ℝ)
    (hk : 0 < radialSq k) (hd : 0 < delta) (hs : RaySeparated k delta)
    (hh : 0 < h) (hM : 0 ≤ M)
    (hsmall : M * h ≤ radialSq k * delta ^ 2 / 174528)
    (herr : |D - h ^ 4 * leadingScalar k| ≤ M * h ^ 5) :
    D ≠ 0 ∧ |D⁻¹| ≤ 174528 / (h ^ 4 * radialSq k * delta ^ 2) := by
  have hl := perturbative_scalar_lower k delta h M D hk hd hs hh hM hsmall herr
  have hb : 0 < h ^ 4 * radialSq k * delta ^ 2 / 174528 := by positivity
  have hp : 0 < |D| := lt_of_lt_of_le hb hl
  refine ⟨abs_pos.mp hp, ?_⟩
  have hr := one_div_le_one_div_of_le hb hl
  simpa only [one_div, inv_div, abs_inv] using hr

/-- **GAC:r8-gap-remainder** (retain the error budget before asserting an inverse). -/
@[ledger "GAC:r8-gap-remainder"]
theorem gapRemainder : Statement.gapRemainder := perturbative_scalar_inverse

/-! ## Non-vacuity -/

-- This is the exact leading model with M=0, not an asserted native finite-h remainder.
example : leadingScalar ![1, 2, 3] ≠ 0 ∧
    |(leadingScalar ![1, 2, 3])⁻¹| ≤ 174528 / (radialSq ![1, 2, 3] * (1 : ℝ) ^ 2) := by
  simpa using perturbative_scalar_inverse ![1, 2, 3] 1 1 0 (leadingScalar ![1, 2, 3])
    (by norm_num [radialSq, Fin.sum_univ_succ]) (by norm_num) separated_123
    (by norm_num) (by norm_num) (by norm_num [radialSq, Fin.sum_univ_succ]) (by norm_num)

end Artform.Scores.GravityBridge.Native.R8
