import ArtformScores.GravityBridge.Native.Retrospective.SourceCostStatements
/-! # The actual solved source and a declared one-multiplication lower bound -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
open Matrix
open Matrix
lemma factorized_schur_same (z : ℚ) :
    schurCovector z = ![-101 * z / 103, -101 * z / 103, 0] := by
  have hr : (torsionBlock.transpose * facePairing) *ᵥ faceInput z = connectionSource z := by
    ext i
    fin_cases i <;>
      simp [torsionBlock, facePairing, faceInput, connectionSource, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hi := full_inverse_source z
  change polynomialInverse kappa *ᵥ connectionSource z = _ at hi
  unfold schurCovector
  rw [native_inverse_identification, hr, hi]
  ext i
  fin_cases i <;>
    norm_num [kappa, facePairing, torsionBlock, faceInput, connectionSource,
      Matrix.mul_apply, Matrix.mulVec, Matrix.one_apply, dotProduct, Fin.sum_univ_succ] <;> ring
lemma one_multiply_original_output (z : ℚ) : oneMultiplySchur z = schurCovector z := by
  rw [factorized_schur_same]
  ext i
  fin_cases i <;> simp [oneMultiplySchur] <;> ring
lemma no_zero_cost_wire : ¬∃ w : ZeroCostWire,
    ∀ z : ℚ, wireValue w z = oneMultiplySchur z 0 := by
  rintro ⟨w, hw⟩
  cases w with
  | input => have h := hw 1; norm_num [wireValue, oneMultiplySchur] at h
  | negativeInput => have h := hw 1; norm_num [wireValue, oneMultiplySchur] at h
  | constant c =>
    have h0 := hw 0
    have h1 := hw 1
    norm_num [wireValue, oneMultiplySchur] at h0 h1
    linarith
/-- **GAC2:selected-source-work-audit**
(the actual solved source and a declared one-multiplication lower bound). -/
@[ledger "GAC2:selected-source-work-audit"]
theorem sourceCostLaw : Statement.sourceCostLaw := by
  exact ⟨factorized_schur_same,
    one_multiply_original_output,
    no_zero_cost_wire⟩
/-! ## Non-vacuity -/
example : oneMultiplySchur 103 = ![-101, -101, 0] := by decide +kernel
end Artform.Scores.GravityBridge.Native.Retrospective
