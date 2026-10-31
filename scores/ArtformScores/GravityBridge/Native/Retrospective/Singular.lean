import ArtformScores.GravityBridge.Native.Retrospective.SingularStatements
/-! # Singular strata and retained source range guards -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
open Matrix
open Full40
open Matrix
lemma distinct_positive_singular :
    paramConnection (1 / 4) *ᵥ ![1, -1, -1] = 0 ∧
      (![1, -1, -1] : Fin 3 → ℚ) ≠ 0 := by decide +kernel
lemma distinct_negative_singular :
    paramConnection (-1 / 2) *ᵥ ![0, -1, 1] = 0 ∧
      (![0, -1, 1] : Fin 3 → ℚ) ≠ 0 := by decide +kernel
lemma repeated_positive_singular : ∀ b : Fin 4,
    repeatedBlock b 1 *ᵥ ![1, 1, 1] = 0 ∧
      (![1, 1, 1] : Fin 3 → ℚ) ≠ 0 := by decide +kernel
lemma repeated_negative_singular : ∀ b : Fin 4,
    repeatedBlock b (-1 / 2) *ᵥ ![1, -1, 0] = 0 ∧
      (![1, -1, 0] : Fin 3 → ℚ) ≠ 0 := by decide +kernel
lemma source_solve_at_global_singularity (z : ℚ) :
    paramConnection (1 / 4) *ᵥ spectralPreparation (1 / 4) z +
      (2 * (1 / 4 : ℚ)) • connectionSource z = 0 := by
  exact spectral_preparation_equation _ z (by norm_num)
lemma false_denominator_cleared_inverse :
    inverseDenominator (1 / 4) = 0 ∧ polynomialInverse (1 / 4) = 0 ∧
      paramConnection (1 / 4) * polynomialInverse (1 / 4) ≠ 1 := by
  decide +kernel
lemma repeated_source_range (r : Fin 3 → ℚ)
    (h : ∃ a, repeatedBlock 0 1 *ᵥ a = r) : r 0 + r 1 + r 2 = 0 := by
  rcases h with ⟨a, rfl⟩
  simp [repeatedBlock, Full40.eta, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring
lemma distinct_source_range (r : Fin 3 → ℚ)
    (h : ∃ a, paramConnection (1 / 4) *ᵥ a = r) : r 0 - r 1 - r 2 = 0 := by
  rcases h with ⟨a, rfl⟩
  simp [paramConnection, curvatureBlock, torsionBlock, facePairing, Matrix.mulVec, dotProduct,
    Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_succ]
  ring
/-- **GAC2:native-singular-source-strata**
(singular strata and retained source range guards). -/
@[ledger "GAC2:native-singular-source-strata"]
theorem singularLaw : Statement.singularLaw := by
  exact ⟨distinct_positive_singular,
    distinct_negative_singular,
    repeated_positive_singular,
    repeated_negative_singular,
    source_solve_at_global_singularity,
    false_denominator_cleared_inverse,
    repeated_source_range,
    distinct_source_range⟩
/-! ## Non-vacuity -/
example : paramConnection kappa * polynomialInverse kappa = 1 :=
  (polynomial_inverse_both kappa (by norm_num [kappa]) (by norm_num [kappa])).1
end Artform.Scores.GravityBridge.Native.Retrospective
