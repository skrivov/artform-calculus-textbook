import ArtformScores.GravityBridge.Native.Retrospective.BlockProgramsStatements
/-! # Verified exact arithmetic programs for the original native block -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
open Matrix
open Matrix
lemma block_program_costs : validProgram 0 denseBlockProgram = true ∧
    validProgram 0 rankBlockProgram = true ∧
    scaleCount denseBlockProgram = 9 ∧ addCount denseBlockProgram = 6 ∧
    scaleCount rankBlockProgram = 4 ∧ addCount rankBlockProgram = 5 := by decide +kernel
lemma block_programs_same (z : Fin 3 → ℚ) :
    programOutput denseBlockProgram ![4, 9, 14] z =
      programOutput rankBlockProgram ![6, 7, 8] z := by
  ext i
  fin_cases i <;>
    norm_num [programOutput, runScalarProgram, evaluateGate, resolveRef, denseBlockProgram,
      rankBlockProgram] <;> ring
lemma rank_program_original_inverse (z : Fin 3 → ℚ) :
    programOutput rankBlockProgram ![6, 7, 8] z = connectionBlock⁻¹ *ᵥ z := by
  rw [native_inverse_identification, native_inverse_polynomial]
  ext i
  fin_cases i <;>
    norm_num [programOutput, runScalarProgram, evaluateGate, resolveRef, rankBlockProgram,
      curvatureBlock, Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.sum_univ_succ] <;> ring
lemma dense_program_original_inverse (z : Fin 3 → ℚ) :
    programOutput denseBlockProgram ![4, 9, 14] z = connectionBlock⁻¹ *ᵥ z := by
  rw [block_programs_same, rank_program_original_inverse]
lemma block_outputs_valid :
    (∀ i : Fin 3, (![4, 9, 14] : Fin 3 → ℕ) i < denseBlockProgram.length) ∧
    (∀ i : Fin 3, (![6, 7, 8] : Fin 3 → ℕ) i < rankBlockProgram.length) := by decide +kernel

/-- **GAC2:verified-native-block-programs**
(verified exact arithmetic programs for the original native block). -/
@[ledger "GAC2:verified-native-block-programs"]
theorem blockProgramsLaw : Statement.blockProgramsLaw := by
  exact ⟨block_program_costs,
    block_programs_same,
    rank_program_original_inverse,
    dense_program_original_inverse,
    block_outputs_valid⟩
/-! ## Non-vacuity -/
example : programOutput rankBlockProgram ![6, 7, 8] ![1, 0, 0] =
    ![-9595 / 19982, -9999 / 19982, -9999 / 19982] := by decide +kernel
end Artform.Scores.GravityBridge.Native.Retrospective
