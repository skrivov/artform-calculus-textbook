import ArtformScores.NonabelianGravity.NonlinearIsotropicAction

/-! # Exact local nonlinear lapse constraint, without a Taylor extrapolation -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearIsotropic

noncomputable def boostCoefficient (C : ℝ) : ℝ :=
  (C + 1) * (1 + 2 * C - C ^ 2) / 2 - 2 / 101

lemma boost_coefficient_positive (C : ℝ) (hC : 1 ≤ C) (hC' : C ≤ 3 / 2) :
    0 < boostCoefficient C := by
  let u := C - 1
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hu' : u ≤ 1 / 2 := by dsimp [u]; linarith
  have h₂ := mul_nonneg hu (sub_nonneg.mpr hu')
  have h₃ := mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu')
  dsimp [boostCoefficient]
  dsimp [u] at h₂ h₃
  nlinarith

lemma force_factorization (C S ell a c : ℝ) (h : C ^ 2 - S ^ 2 = 1) :
    lapseForceAt (1 / 101) C S ell a c =
      3 * a * ((C - 1) * boostCoefficient C + (1 / 101) * ((c - a) ^ 2 / ell ^ 2)) := by
  dsimp [lapseForceAt, closedLapse, boostCoefficient]
  linear_combination -(3 / 2) * a * (1 + 2 * C - C ^ 2) * h

lemma force_nonnegative (C S ell a c : ℝ) (ha : 0 < a)
    (hC : 1 ≤ C) (hC' : C ≤ 3 / 2) (h : C ^ 2 - S ^ 2 = 1) :
    0 ≤ lapseForceAt (1 / 101) C S ell a c := by
  rw [force_factorization C S ell a c h]
  exact mul_nonneg (by positivity) (add_nonneg
    (mul_nonneg (by linarith) (le_of_lt (boost_coefficient_positive C hC hC')))
    (mul_nonneg (by norm_num) (div_nonneg (sq_nonneg _) (sq_nonneg _))))

lemma force_positive_boost (C S ell a c : ℝ) (ha : 0 < a)
    (hC : 1 ≤ C) (hC' : C ≤ 3 / 2) (h : C ^ 2 - S ^ 2 = 1) (hS : S ≠ 0) :
    0 < lapseForceAt (1 / 101) C S ell a c := by
  have hc : 1 < C := by nlinarith [sq_pos_of_ne_zero hS]
  rw [force_factorization C S ell a c h]
  exact mul_pos (by positivity) (add_pos_of_pos_of_nonneg
    (mul_pos (by linarith) (boost_coefficient_positive C hC hC'))
    (mul_nonneg (by norm_num) (div_nonneg (sq_nonneg _) (sq_nonneg _))))

lemma zero_force_iff (C S ell a c : ℝ) (he : ell ≠ 0) (ha : 0 < a)
    (hC : 1 ≤ C) (hC' : C ≤ 3 / 2) (h : C ^ 2 - S ^ 2 = 1) :
    lapseForceAt (1 / 101) C S ell a c = 0 ↔ S = 0 ∧ c = a := by
  constructor
  · intro hf
    have hs : S = 0 := by
      by_contra hn
      have hp := force_positive_boost C S ell a c ha hC hC' h hn
      linarith
    have hc : C = 1 := by rw [hs] at h; nlinarith
    subst C
    rw [force_factorization _ _ _ _ _ h] at hf
    have hp : 0 < 3 * a * (1 / 101) / ell ^ 2 := by positivity
    refine ⟨hs, ?_⟩
    have heq : (3 * a * (1 / 101) / ell ^ 2) * (c - a) ^ 2 = 0 := by
      linear_combination hf
    have hz := (mul_eq_zero.mp heq).resolve_left (ne_of_gt hp)
    nlinarith [sq_nonneg (c - a)]
  · rintro ⟨hs, hc⟩
    have hcc : C = 1 := by rw [hs] at h; nlinarith
    simp [lapseForceAt, closedLapse, hs, hc, hcc]

lemma lapse_derivative_nonzero (C S ell a c : ℝ) (he : ell ≠ 0) (ha : 0 < a)
    (hC : 1 ≤ C) (hC' : C ≤ 3 / 2) (h : C ^ 2 - S ^ 2 = 1) (hS : S ≠ 0) :
    deriv (fun N => totalAction (1 / 101) C S N a c) ell ≠ 0 := by
  rw [(lapse_derivative_at (1 / 101) C S ell a c he (ne_of_gt ha) h).deriv]
  exact ne_of_gt (force_positive_boost C S ell a c ha hC hC' h hS)

end Artform.Scores.NonabelianGravity.NonlinearIsotropic
