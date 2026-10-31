import ArtformScores.GravityBridge.GaussianStatements

/-! # Gaussian elimination includes the actual Lebesgue normalization -/

namespace Artform.Scores.GravityBridge

noncomputable section

open MeasureTheory


lemma gaussian_square (a b c j k q z : ℝ) (ha : a ≠ 0) :
    gaussianAction a b c j k q z = gaussianEffective a b c j k q +
      a * (z - gaussianCenter a b j q) ^ 2 := by
  dsimp [gaussianAction, gaussianEffective, gaussianCenter]
  field_simp
  ring

lemma gaussian_schur_integral (a b c j k q : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℝ => Real.exp (-gaussianAction a b c j k q z)) ∧
    (∫ z : ℝ, Real.exp (-gaussianAction a b c j k q z)) =
      Real.exp (-gaussianEffective a b c j k q) * Real.sqrt (Real.pi / a) := by
  have hf : (fun z : ℝ => Real.exp (-gaussianAction a b c j k q z)) =
      fun z => Real.exp (-gaussianEffective a b c j k q) *
        Real.exp (-a * (z - gaussianCenter a b j q) ^ 2) := by
    funext z
    rw [gaussian_square a b c j k q z (ne_of_gt ha)]
    rw [show -(gaussianEffective a b c j k q + a * (z - gaussianCenter a b j q) ^ 2) =
      -gaussianEffective a b c j k q + -a * (z - gaussianCenter a b j q) ^ 2 by ring,
      Real.exp_add]
  rw [hf]
  constructor
  · exact ((integrable_exp_neg_mul_sq ha).comp_sub_right (gaussianCenter a b j q)).const_mul _
  · rw [integral_const_mul,
      integral_sub_right_eq_self (fun z : ℝ => Real.exp (-a * z ^ 2)) (gaussianCenter a b j q),
      integral_gaussian]

lemma gaussian_determinant (a b c : ℝ) (ha : a ≠ 0) :
    Matrix.det (!![c, b; b, a] : Matrix (Fin 2) (Fin 2) ℝ) = a * (c - b ^ 2 / a) := by
  simp [Matrix.det_fin_two]
  field_simp

/-- **GAC:gaussian-schur-integral** (an actual convergent integral with source terms). -/
@[ledger "GAC:gaussian-schur-integral"]
theorem gaussianLaw : Statement.gaussianLaw := by
  refine ⟨gaussian_square, gaussian_schur_integral, gaussian_determinant, ?_⟩
  rw [integrable_exp_neg_mul_sq_iff]
  norm_num

/-! ## Non-vacuity -/

example : gaussianEffective 2 1 3 4 5 1 = -23 / 2 ∧
    gaussianCenter 2 1 4 1 = 3 / 2 ∧
    Matrix.det (!![(3 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) = 5 := by
  norm_num [gaussianEffective, gaussianCenter, Matrix.det_fin_two]

example : ¬ Integrable (fun z : ℝ => Real.exp (-(0 : ℝ) * z ^ 2)) := by
  rw [integrable_exp_neg_mul_sq_iff]
  norm_num

end

end Artform.Scores.GravityBridge
