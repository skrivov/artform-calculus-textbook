import ArtformScores.GravityBridge.Native.Retrospective.PolynomialInverseStatements

/-! # The original signed block through a quadratic matrix relation -/

namespace Artform.Scores.GravityBridge.Native.Retrospective

open Matrix



open Matrix

lemma curvature_minimal_relation : curvatureBlock * curvatureBlock =
    curvatureBlock + (2 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) := by decide +kernel
lemma torsion_gram_relation : torsionBlock.transpose * facePairing * torsionBlock =
    -(curvatureBlock + (2 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ)) := by decide +kernel
lemma parameter_block_factor (t : ℚ) :
    paramConnection t = (1 - 2 * t) • curvatureBlock - (4 * t) • 1 := by
  rw [paramConnection, torsion_gram_relation]
  module
lemma polynomial_product (t : ℚ) :
    paramConnection t * inverseNumerator t = inverseDenominator t • 1 := by
  rw [parameter_block_factor]
  simp only [inverseNumerator, sub_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.one_mul, smul_smul]
  rw [curvature_minimal_relation]
  dsimp [inverseDenominator]
  module
lemma polynomial_product_reverse (t : ℚ) :
    inverseNumerator t * paramConnection t = inverseDenominator t • 1 := by
  rw [parameter_block_factor]
  simp only [inverseNumerator, mul_sub, add_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.one_mul, smul_smul]
  rw [curvature_minimal_relation]
  dsimp [inverseDenominator]
  module
lemma inverse_denominator_ne_zero (t : ℚ) (hp : 1 - 4 * t ≠ 0) (hm : 1 + 2 * t ≠ 0) :
    inverseDenominator t ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) hp) hm
lemma polynomial_inverse_both (t : ℚ) (hp : 1 - 4 * t ≠ 0) (hm : 1 + 2 * t ≠ 0) :
    paramConnection t * polynomialInverse t = 1 ∧
    polynomialInverse t * paramConnection t = 1 := by
  have hd := inverse_denominator_ne_zero t hp hm
  constructor
  · rw [polynomialInverse, Matrix.mul_smul, polynomial_product, smul_smul, inv_mul_cancel₀ hd,
      one_smul]
  · rw [polynomialInverse, Matrix.smul_mul, polynomial_product_reverse, smul_smul,
      inv_mul_cancel₀ hd, one_smul]
lemma native_parameter_block : paramConnection kappa = connectionBlock := rfl
lemma native_inverse_polynomial : polynomialInverse kappa =
    (1 / 19982 : ℚ) • ((9999 : ℚ) • curvatureBlock - (9595 : ℚ) • 1) := by
  norm_num [polynomialInverse, inverseNumerator, inverseDenominator, kappa]
  module

lemma polynomial_is_inverse (t : ℚ) (hp : 1 - 4 * t ≠ 0) (hm : 1 + 2 * t ≠ 0) :
    (paramConnection t)⁻¹ = polynomialInverse t :=
  Matrix.inv_eq_right_inv (polynomial_inverse_both t hp hm).1
lemma native_inverse_identification : connectionBlock⁻¹ = polynomialInverse kappa := by
  rw [← native_parameter_block]
  exact polynomial_is_inverse kappa (by norm_num [kappa]) (by norm_num [kappa])

/-- **GAC2:signed-block-polynomial-inverse**
(the original signed block through a quadratic matrix relation). -/
@[ledger "GAC2:signed-block-polynomial-inverse"]
theorem polynomialInverseLaw : Statement.polynomialInverseLaw := by
  exact ⟨curvature_minimal_relation,
    torsion_gram_relation,
    parameter_block_factor,
    polynomial_product,
    polynomial_product_reverse,
    inverse_denominator_ne_zero,
    polynomial_inverse_both,
    native_parameter_block,
    native_inverse_polynomial,
    polynomial_is_inverse,
    native_inverse_identification⟩

/-! ## Non-vacuity -/
example : paramConnection kappa * polynomialInverse kappa = 1 ∧
    polynomialInverse kappa * paramConnection kappa = 1 :=
  polynomial_inverse_both kappa (by norm_num [kappa]) (by norm_num [kappa])

end Artform.Scores.GravityBridge.Native.Retrospective
