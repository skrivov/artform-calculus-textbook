import ArtformScores.GravityBridge.Native.R8Statements

/-! # Native leading angular factor with an explicit global ray-distance bound -/

namespace Artform.Scores.GravityBridge.Native.R8

open Finset

lemma radialSq_nonneg (k : Fin 3 → ℝ) : 0 ≤ radialSq k :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (k i))

lemma projected_norm_identity (k : Fin 3 → ℝ) (hk : radialSq k ≠ 0) :
    (∑ i, (projectedSquare k i) ^ 2) = angularDefect k := by
  dsimp [projectedSquare, angularDefect]
  simp only [Fin.sum_univ_succ]
  field_simp [hk]
  simp [radialSq, Fin.sum_univ_succ]
  ring

lemma angular_homogeneous (k : Fin 3 → ℝ) (t : ℝ) :
    angularDefect (fun i => t * k i) = t ^ 4 * angularDefect k := by
  by_cases ht : t = 0
  · subst t
    simp [angularDefect, radialSq]
  by_cases hk : radialSq k = 0
  · have hz : ∀ i, k i = 0 := by
      intro i
      have he : (k i) ^ 2 ≤ radialSq k := by
        exact Finset.single_le_sum (fun j _ => sq_nonneg (k j)) (Finset.mem_univ i)
      rw [hk] at he
      nlinarith [sq_nonneg (k i)]
    simp [angularDefect, radialSq, hz]
  have hr : radialSq (fun i => t * k i) = t ^ 2 * radialSq k := by
    simp [radialSq, Fin.sum_univ_succ]
    ring
  dsimp [angularDefect]
  rw [hr]
  field_simp [ht, hk]
  simp [radialSq, Fin.sum_univ_succ]
  ring

lemma angular_numerator (k : Fin 3 → ℝ) (hk : radialSq k ≠ 0) :
    radialSq k * angularDefect k = pairNumerator k := by
  dsimp [angularDefect]
  field_simp [hk]
  simp [radialSq, pairNumerator, Fin.sum_univ_succ]
  ring

lemma nearest_square (u m : ℝ) :
    m ^ 2 * (if u ^ 2 ≤ (u - m) ^ 2 then u ^ 2 else (u - m) ^ 2) ≤
      4 * u ^ 2 * (u - m) ^ 2 := by
  split_ifs with h
  · have hb : m ^ 2 ≤ 4 * (u - m) ^ 2 := by nlinarith [sq_nonneg (2 * u - m)]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg u)]
  · have hb : m ^ 2 ≤ 4 * u ^ 2 := by nlinarith [sq_nonneg (2 * u - m)]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg (u - m))]

lemma pivot_pair_bound (k : Fin 3 → ℝ) (j : Fin 3) :
    (k j) ^ 2 * (∑ i, (k i) ^ 2 * (k i - k j) ^ 2) ≤ pairNumerator k := by
  fin_cases j <;> simp [pairNumerator, Fin.sum_univ_succ] <;>
    nlinarith [sq_nonneg (k 0 * k 1 * (k 0 - k 1)),
      sq_nonneg (k 0 * k 2 * (k 0 - k 2)), sq_nonneg (k 1 * k 2 * (k 1 - k 2))]

lemma angular_ray_witness (k : Fin 3 → ℝ) (hk : 0 < radialSq k) :
    ∃ m b, m ≠ 0 ∧ (∃ i, b i = true) ∧
      radialSq k * rayError k m b ≤ 36 * angularDefect k := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun i => (k i) ^ 2) (by simp)
  have hbound : radialSq k ≤ 3 * (k j) ^ 2 := by
    have h0 := hmax 0 (by simp)
    have h1 := hmax 1 (by simp)
    have h2 := hmax 2 (by simp)
    dsimp [radialSq]
    simp only [Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Fin.sum_univ_zero, add_zero]
    linarith
  have hm : k j ≠ 0 := by intro he; rw [he] at hbound; nlinarith
  let b : Fin 3 → Bool := fun i => if (k i) ^ 2 ≤ (k i - k j) ^ 2 then false else true
  have hbj : b j = true := by simp [b, hm]
  have hsum : (k j) ^ 2 * rayError k (k j) b ≤
      4 * ∑ i, (k i) ^ 2 * (k i - k j) ^ 2 := by
    dsimp [rayError]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := nearest_square (k i) (k j)
    by_cases he : (k i) ^ 2 ≤ (k i - k j) ^ 2
    · simpa [rayPoint, b, he, mul_assoc] using h
    · simpa [rayPoint, b, he, mul_assoc] using h
  have hdist : 0 ≤ rayError k (k j) b := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg (k j))
  have hpair := pivot_pair_bound k j
  have hmain : (k j) ^ 4 * rayError k (k j) b ≤ 4 * pairNumerator k := by nlinarith
  have hr : (radialSq k) ^ 2 ≤ 9 * (k j) ^ 4 := by
    have h := mul_self_le_mul_self (radialSq_nonneg k) hbound
    nlinarith
  have htotal := mul_le_mul_of_nonneg_right hr hdist
  have hn := angular_numerator k (ne_of_gt hk)
  refine ⟨k j, b, hm, ⟨j, hbj⟩, ?_⟩
  have hfinal : radialSq k * (radialSq k * rayError k (k j) b -
      36 * angularDefect k) ≤ 0 := by nlinarith
  by_contra he
  have hgap : 0 < radialSq k * rayError k (k j) b - 36 * angularDefect k := by linarith
  have hpositive := mul_pos hk hgap
  linarith

lemma angular_separation_bound (k : Fin 3 → ℝ) (delta : ℝ)
    (hk : 0 < radialSq k) (hs : RaySeparated k delta) :
    radialSq k * delta ^ 2 ≤ 36 * angularDefect k := by
  obtain ⟨m, b, hm, hb, he⟩ := angular_ray_witness k hk
  have hd := hs m b hb
  have h := mul_le_mul_of_nonneg_left hd (radialSq_nonneg k)
  linarith

lemma separated_123 : RaySeparated ![1, 2, 3] 1 := by
  intro m b hb
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
    norm_num [rayError, rayPoint, Fin.sum_univ_succ, h0, h1, h2] <;>
    nlinarith [sq_nonneg (m - 1), sq_nonneg (m - 2), sq_nonneg (m - 3),
      sq_nonneg (m - 3 / 2), sq_nonneg (m - 5 / 2)]

lemma metricCoefficient_lower : (1 / (24 * 101) : ℝ) < (metricCoefficient : ℝ) := by
  norm_num [metricCoefficient]

lemma leading_scalar_lower (k : Fin 3 → ℝ) (delta : ℝ)
    (hk : 0 < radialSq k) (hd : 0 < delta) (hs : RaySeparated k delta) :
    radialSq k * delta ^ 2 / 87264 ≤ |leadingScalar k| := by
  have hg := angular_separation_bound k delta hk hs
  have hdp : 0 < delta ^ 2 := sq_pos_of_pos hd
  have hp : 0 < angularDefect k := by nlinarith [mul_pos hk hdp]
  have hc := metricCoefficient_lower
  have hcp : 0 < (metricCoefficient : ℝ) := by linarith
  have he : |leadingScalar k| = (metricCoefficient : ℝ) * angularDefect k := by
    dsimp [leadingScalar]
    rw [neg_mul, abs_neg, abs_of_pos (mul_pos hcp hp)]
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hc) (le_of_lt hp)]

lemma leading_scalar_inverse (k : Fin 3 → ℝ) (delta : ℝ)
    (hk : 0 < radialSq k) (hd : 0 < delta) (hs : RaySeparated k delta) :
    leadingScalar k ≠ 0 ∧ |(leadingScalar k)⁻¹| ≤ 87264 / (radialSq k * delta ^ 2) := by
  have hl := leading_scalar_lower k delta hk hd hs
  have hb : 0 < radialSq k * delta ^ 2 / 87264 := by positivity
  have hp : 0 < |leadingScalar k| := lt_of_lt_of_le hb hl
  refine ⟨abs_pos.mp hp, ?_⟩
  have hr := one_div_le_one_div_of_le hb hl
  simpa only [one_div, inv_div, abs_inv] using hr

lemma leading_scalar_homogeneous (k : Fin 3 → ℝ) (t : ℝ) :
    leadingScalar (fun i => t * k i) = t ^ 4 * leadingScalar k := by
  dsimp [leadingScalar]
  rw [angular_homogeneous]
  ring

/-- **GAC:r8-angular-conditioning** (explicit conditioning of the native leading metric-cut
  scalar). -/
@[ledger "GAC:r8-angular-conditioning"]
theorem angularConditioning : Statement.angularConditioning := by
  refine ⟨?_, angular_ray_witness, angular_separation_bound, metricCoefficient_lower,
    leading_scalar_inverse⟩
  intro k hk
  exact ⟨projected_norm_identity k hk, angular_numerator k hk⟩

/-! ## Non-vacuity -/

example : radialSq ![1, 2, 3] = 14 ∧ angularDefect ![1, 2, 3] = 38 / 7 := by
  norm_num [radialSq, angularDefect, Fin.sum_univ_succ]

example : angularDefect ![1, 0, 0] = 0 ∧ ¬ RaySeparated ![1, 0, 0] 1 := by
  constructor
  · norm_num [angularDefect, radialSq, Fin.sum_univ_succ]
  · intro h
    have he := h 1 ![true, false, false] ⟨0, rfl⟩
    norm_num [rayError, rayPoint, Fin.sum_univ_succ] at he

example : RaySeparated ![1, 2, 3] 1 ∧ leadingScalar ![1, 2, 3] ≠ 0 := by
  exact ⟨separated_123, (leading_scalar_inverse _ 1 (by norm_num [radialSq,
    Fin.sum_univ_succ]) (by norm_num) separated_123).1⟩

end Artform.Scores.GravityBridge.Native.R8
