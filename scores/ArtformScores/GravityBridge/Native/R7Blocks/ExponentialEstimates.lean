import ArtformScores.GravityBridge.Stability
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Contractive projection power bounds and exponential off-block remainder -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks
variable {R : Type*} [NormedRing R] [NormOneClass R]

def offPower (P A : R) (n : ℕ) : R := (1 - P) * A ^ n * P
def compressed (P A : R) : R := (1 - P) * A * (1 - P)

omit [NormOneClass R] in
lemma complementary_projection (P : R) (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P ∧ (1 - P) * P = 0 := by
  constructor
  · calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  · rw [sub_mul,one_mul,hP,sub_self]

omit [NormOneClass R] in
lemma off_power_recursion (P A : R) (hP : P * P = P) (n : ℕ) :
    offPower P A (n + 1) = compressed P A * offPower P A n + offPower P A 1 * A ^ n * P := by
  have hQ := (complementary_projection P hP).1
  have hc : compressed P A * offPower P A n = (1 - P) * A * (1 - P) * A ^ n * P := by
    change (1 - P) * A * (1 - P) * ((1 - P) * A ^ n * P) = (1 - P) * A * (1 - P) * A ^ n * P
    calc
      _ = (1 - P) * A * ((1 - P) * (1 - P)) * A ^ n * P := by noncomm_ring
      _ = _ := by rw [hQ]
  rw [hc]
  simp only [offPower,pow_succ']
  noncomm_ring

omit [NormOneClass R] in
lemma off_power_zero (P A : R) (hP : P * P = P) : offPower P A 0 = 0 := by
  simpa [offPower] using (complementary_projection P hP).2

omit [NormOneClass R] in
lemma norm_compressed_le (P A : R) (a : ℝ) (hQ : ‖1 - P‖ ≤ 1) (hA : ‖A‖ ≤ a) :
    ‖compressed P A‖ ≤ a := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hA
  calc
    _ ≤ (‖1 - P‖ * ‖A‖) * ‖1 - P‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * a * 1 := by gcongr
    _ = a := by ring

lemma norm_power_projected_le (P A : R) (a : ℝ) (n : ℕ)
    (hP : ‖P‖ ≤ 1) (hA : ‖A‖ ≤ a) : ‖A ^ n * P‖ ≤ a ^ n := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hA
  calc
    _ ≤ ‖A ^ n‖ * ‖P‖ := norm_mul_le _ _
    _ ≤ ‖A‖ ^ n * ‖P‖ := mul_le_mul_of_nonneg_right (norm_pow_le _ _) (norm_nonneg _)
    _ ≤ a ^ n * 1 := by gcongr
    _ = a ^ n := mul_one _

lemma norm_off_power_le (P A : R) (a : ℝ) (hPP : P * P = P)
    (hP : ‖P‖ ≤ 1) (hQ : ‖1 - P‖ ≤ 1) (hA : ‖A‖ ≤ a) (n : ℕ) :
    ‖offPower P A (n + 1)‖ ≤ (n + 1 : ℝ) * a ^ n * ‖offPower P A 1‖ := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hA
  induction n with
  | zero => simp
  | succ n ih =>
    rw [off_power_recursion P A hPP (n + 1)]
    calc
      _ ≤ ‖compressed P A * offPower P A (n + 1)‖ + ‖offPower P A 1 * A ^ (n + 1) * P‖ :=
        norm_add_le _ _
      _ ≤ ‖compressed P A‖ * ‖offPower P A (n + 1)‖ +
          ‖offPower P A 1‖ * ‖A ^ (n + 1) * P‖ := by
        gcongr
        · exact norm_mul_le _ _
        · simpa only [mul_assoc] using norm_mul_le (offPower P A 1) (A ^ (n + 1) * P)
      _ ≤ a * ((n + 1 : ℝ) * a ^ n * ‖offPower P A 1‖) + ‖offPower P A 1‖ * a ^ (n + 1) := by
        gcongr
        · exact norm_compressed_le P A a hQ hA
        · exact norm_power_projected_le P A a (n + 1) hP hA
      _ = (((n + 1 : ℕ) : ℝ) + 1) * a ^ (n + 1) * ‖offPower P A 1‖ := by
        push_cast
        rw [pow_succ]
        ring


section Analytic
variable [NormedAlgebra ℝ R] [CompleteSpace R]

noncomputable def offExpTerm (P A : R) (h : ℝ) (n : ℕ) : R :=
  ((n.factorial : ℝ)⁻¹ * h ^ n) • offPower P A n

omit [NormOneClass R] in
lemma off_exp_hasSum (P A : R) (h : ℝ) :
    HasSum (offExpTerm P A h) ((1 - P) * NormedSpace.exp (h • A) * P) := by
  have hs := ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (h • A)).mul_left (1 - P)).mul_right P
  convert hs using 1
  ext n
  simp [offExpTerm,offPower,smul_pow,smul_smul]

omit [NormOneClass R] in
lemma off_exp_tail_hasSum (P A : R) (h : ℝ) (hPP : P * P = P) :
    HasSum (fun n => offExpTerm P A h (n + 2))
      ((1 - P) * NormedSpace.exp (h • A) * P - h • offPower P A 1) := by
  have hs := (hasSum_nat_add_iff' 2).2 (off_exp_hasSum P A h)
  simpa [Finset.sum_range_succ,offExpTerm,off_power_zero P A hPP] using hs

omit [CompleteSpace R] in
lemma off_exp_term_bound (P A : R) (h a : ℝ) (n : ℕ) (hh : 0 ≤ h)
    (hPP : P * P = P) (hP : ‖P‖ ≤ 1) (hQ : ‖1 - P‖ ≤ 1) (hA : ‖A‖ ≤ a) :
    ‖offExpTerm P A h (n + 2)‖ ≤
      (h * ‖offPower P A 1‖) * ((h * a) ^ (n + 1) / (n + 1).factorial) := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hA
  have hc : 0 ≤ ((n + 2).factorial : ℝ)⁻¹ * h ^ (n + 2) := by positivity
  rw [offExpTerm,norm_smul,Real.norm_of_nonneg hc]
  calc
    _ ≤ (((n + 2).factorial : ℝ)⁻¹ * h ^ (n + 2)) *
        ((n + 2 : ℝ) * a ^ (n + 1) * ‖offPower P A 1‖) := by
      gcongr
      convert norm_off_power_le P A a hPP hP hQ hA (n + 1) using 1
      norm_num [Nat.cast_add,add_assoc]
    _ = _ := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring

lemma scalar_exp_tail_hasSum (h a : ℝ) :
    HasSum (fun n : ℕ => (h * a) ^ (n + 1) / (n + 1).factorial)
      (Real.exp (h * a) - 1) := by
  have hs := (hasSum_nat_add_iff' 1).2
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (h * a))
  simpa [Finset.sum_range_succ,div_eq_mul_inv,mul_comm,Real.exp_eq_exp_ℝ] using hs

omit [NormOneClass R] in
lemma scalar_exp_tail_nonnegative (h a : ℝ) (hh : 0 ≤ h) (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ (h * a) ^ (n + 1) / (n + 1).factorial := by positivity

lemma off_exp_remainder_bound (P A : R) (h a : ℝ) (hh : 0 ≤ h)
    (hPP : P * P = P) (hP : ‖P‖ ≤ 1) (hQ : ‖1 - P‖ ≤ 1) (hA : ‖A‖ ≤ a) :
    ‖(1 - P) * NormedSpace.exp (h • A) * P - h • offPower P A 1‖ ≤
      h * ‖offPower P A 1‖ * (Real.exp (h * a) - 1) := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hA
  have hs := (scalar_exp_tail_hasSum h a).mul_left (h * ‖offPower P A 1‖)
  have hb := fun n => off_exp_term_bound P A h a n hh hPP hP hQ hA
  have hn : Summable (fun n => ‖offExpTerm P A h (n + 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs.summable
  rw [← (off_exp_tail_hasSum P A h hPP).tsum_eq]
  exact (norm_tsum_le_tsum_norm hn).trans
    ((Summable.tsum_le_tsum hb hn hs.summable).trans_eq hs.tsum_eq)

lemma one_step_offblock_implies_generator (P A : R) (h a : ℝ) (hh : 0 < h)
    (hPP : P * P = P) (hP : ‖P‖ ≤ 1) (hQ : ‖1 - P‖ ≤ 1) (hA : ‖A‖ ≤ a)
    (hsmall : Real.exp (h * a) - 1 < 1)
    (hstep : (1 - P) * NormedSpace.exp (h • A) * P = 0) : (1 - P) * A * P = 0 := by
  have hb := off_exp_remainder_bound P A h a hh.le hPP hP hQ hA
  rw [hstep,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hh.le] at hb
  have hn := norm_nonneg (offPower P A 1)
  have hz : ‖offPower P A 1‖ = 0 := by
    by_contra hnz
    have hp : 0 < h * ‖offPower P A 1‖ := mul_pos hh (lt_of_le_of_ne hn (Ne.symm hnz))
    exact (not_lt_of_ge hb) (mul_lt_of_lt_one_right hp hsmall)
  simpa [offPower] using norm_eq_zero.mp hz

end Analytic
end Artform.Scores.GravityBridge.Native.R7Blocks
