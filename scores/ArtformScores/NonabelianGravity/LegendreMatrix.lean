import ArtformScores.NonabelianGravity.LegendreMatrixData

/-! # Checked rational certificates for the native singular Legendre rank -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Legendre

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
-- Check the complete rational product, including every zero entry.
lemma mixed_factorization : mixed = leftFactor * rightFactor := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
-- The left factor has an exact left inverse, not just a nonzero minor guess.
lemma factor_left_inverse : leftInverse * leftFactor = 1 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
-- The right factor has an exact right inverse; together these certify rank24.
lemma factor_right_inverse : rightFactor * rightInverse = 1 := by decide +kernel

lemma mixed_rank : Matrix.rank mixed = 24 := by
  apply le_antisymm
  · rw [mixed_factorization]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · have h : leftInverse * mixed * rightInverse = (1 : Matrix (Fin 24) (Fin 24) ℚ) := by
      rw [mixed_factorization]
      simp only [Matrix.mul_assoc, factor_right_inverse, Matrix.mul_one, factor_left_inverse]
    calc
      24 = Matrix.rank (1 : Matrix (Fin 24) (Fin 24) ℚ) := by simp
      _ = Matrix.rank (leftInverse * mixed * rightInverse) := by rw [h]
      _ ≤ Matrix.rank (leftInverse * mixed) := Matrix.rank_mul_le_left _ _
      _ ≤ Matrix.rank mixed := Matrix.rank_mul_le_right _ _

end Artform.Scores.NonabelianGravity.Legendre
