import ArtformScores.GravityBridge.Native.R8Angular

/-! # Exact loss of uniform leading inverse control near a native exceptional ray -/

namespace Artform.Scores.GravityBridge.Native.R8

open Finset

lemma near_ray_formula (e : ℝ) :
    angularDefect (approachingRay e) = e ^ 2 * (1 + e) ^ 2 / (1 + (1 + e) ^ 2) := by
  have hd : (1 + (1 + e) ^ 2 : ℝ) ≠ 0 := by positivity
  dsimp [angularDefect, radialSq, approachingRay]
  norm_num [Fin.sum_univ_succ]
  field_simp [hd]
  ring

lemma near_ray_bounds (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    (2 ≤ radialSq (approachingRay e) ∧ radialSq (approachingRay e) ≤ 5) ∧
    (0 < angularDefect (approachingRay e) ∧ angularDefect (approachingRay e) ≤ e ^ 2) := by
  have hd : (0 : ℝ) < 1 + (1 + e) ^ 2 := by positivity
  constructor
  · norm_num [radialSq, approachingRay, Fin.sum_univ_succ]
    constructor <;> nlinarith [sq_nonneg e, sq_nonneg (1 - e)]
  · rw [near_ray_formula]
    constructor
    · positivity
    · rw [div_le_iff₀ hd]
      nlinarith [sq_nonneg e]

lemma near_ray_inverse (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    leadingScalar (approachingRay e) ≠ 0 ∧
      1 / ((metricCoefficient : ℝ) * e ^ 2) ≤ |(leadingScalar (approachingRay e))⁻¹| := by
  obtain ⟨hr, hp, hu⟩ := near_ray_bounds e he he1
  have hc : 0 < (metricCoefficient : ℝ) := by have h := metricCoefficient_lower; linarith
  have ha : |leadingScalar (approachingRay e)| =
      (metricCoefficient : ℝ) * angularDefect (approachingRay e) := by
    simp only [leadingScalar, abs_mul, abs_neg, abs_of_pos hc, abs_of_pos hp]
  have hpos := mul_pos hc hp
  have hle := mul_le_mul_of_nonneg_left hu (le_of_lt hc)
  have hn : 0 < |leadingScalar (approachingRay e)| := by rw [ha]; exact hpos
  refine ⟨abs_pos.mp hn, ?_⟩
  rw [abs_inv, ha]
  simpa only [one_div] using one_div_le_one_div_of_le hpos hle

lemma ray_sequence (n : ℕ) :
    let e : ℝ := 1 / (n + 1 : ℝ)
    2 ≤ radialSq (approachingRay e) ∧ radialSq (approachingRay e) ≤ 5 ∧
      leadingScalar (approachingRay e) ≠ 0 ∧
      (n + 1 : ℝ) ^ 2 / (metricCoefficient : ℝ) ≤ |(leadingScalar (approachingRay e))⁻¹| := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have he : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have he1 : (1 / (n + 1 : ℝ)) ≤ 1 := by
    rw [div_le_one hn]
    linarith
  obtain ⟨hr0, hr1⟩ := (near_ray_bounds (1 / (n + 1 : ℝ)) he he1).1
  obtain ⟨hneq, hb⟩ := near_ray_inverse (1 / (n + 1 : ℝ)) he he1
  refine ⟨hr0, hr1, hneq, ?_⟩
  have hc : (metricCoefficient : ℝ) ≠ 0 := by have h := metricCoefficient_lower; linarith
  have hid : (1 : ℝ) / ((metricCoefficient : ℝ) * (1 / (n + 1 : ℝ)) ^ 2) =
      (n + 1 : ℝ) ^ 2 / (metricCoefficient : ℝ) := by field_simp [hc, ne_of_gt hn]
  rwa [hid] at hb

lemma no_uniform_leading_inverse :
    ¬ ∃ M : ℝ, ∀ n : ℕ,
      |(leadingScalar (approachingRay (1 / (n + 1 : ℝ))))⁻¹| ≤ M := by
  rintro ⟨M, hM⟩
  have hc : 0 < (metricCoefficient : ℝ) := by have h := metricCoefficient_lower; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((metricCoefficient : ℝ) * M + 1)
  have hb := (ray_sequence n).2.2.2
  have hb' := (div_le_iff₀ hc).mp hb
  have ht := mul_le_mul_of_nonneg_right (hM n) (le_of_lt hc)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- **GAC:r8-nonuniform-domain** (a concrete annular adverse sequence and radial scaling). -/
@[ledger "GAC:r8-nonuniform-domain"]
theorem nonuniformDomain : Statement.nonuniformDomain :=
  ⟨near_ray_bounds, ray_sequence, no_uniform_leading_inverse, leading_scalar_homogeneous⟩

/-! ## Non-vacuity -/

example : radialSq (approachingRay 1) = 5 ∧ angularDefect (approachingRay 1) = 4 / 5 ∧
    leadingScalar (approachingRay 1) ≠ 0 := by
  refine ⟨by norm_num [radialSq, approachingRay, Fin.sum_univ_succ],
    by norm_num [angularDefect, radialSq, approachingRay, Fin.sum_univ_succ],
    (near_ray_inverse 1 (by norm_num) (by norm_num)).1⟩

end Artform.Scores.GravityBridge.Native.R8
