import ArtformScores.GravityBridge.Native.GreenComposition.ProgramsStatements

/-! # Matched exact programs for all three native component outputs -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators
open Matrix Retrospective



open Matrix Retrospective

lemma two_cell_program_costs :
    validProgram 0 literalBoundaryProgram = true ∧ validProgram 0 reusedBoundaryProgram = true ∧
    scaleCount literalBoundaryProgram = 4 ∧ addCount literalBoundaryProgram = 4 ∧
    scaleCount reusedBoundaryProgram = 3 ∧ addCount reusedBoundaryProgram = 4 := by decide +kernel

lemma literal_boundary_original_answer (x : Fin 3 → ℚ) :
    programOutput literalBoundaryProgram ![3, 5, 7] x =
      ![sourceMiddle (1 / 101) (x 0) (x 1) (x 2),
        inputMomentum (1 / 101) (x 0) (x 1) (x 2),
        outputMomentum (1 / 101) (x 0) (x 1) (x 2)] := by
  ext i
  fin_cases i <;> norm_num [programOutput, runScalarProgram, evaluateGate, resolveRef,
    literalBoundaryProgram, sourceMiddle, inputMomentum, outputMomentum] <;> ring

lemma reused_boundary_original_answer (x : Fin 3 → ℚ) :
    programOutput reusedBoundaryProgram ![6, 3, 4] x =
      ![sourceMiddle (1 / 101) (x 0) (x 1) (x 2),
        inputMomentum (1 / 101) (x 0) (x 1) (x 2),
        outputMomentum (1 / 101) (x 0) (x 1) (x 2)] := by
  ext i
  fin_cases i <;> norm_num [programOutput, runScalarProgram, evaluateGate, resolveRef,
    reusedBoundaryProgram, sourceMiddle, inputMomentum, outputMomentum] <;> ring

lemma matched_boundary_programs (x : Fin 3 → ℚ) :
    programOutput literalBoundaryProgram ![3, 5, 7] x = programOutput reusedBoundaryProgram ![6,
      3, 4] x := by
  rw [literal_boundary_original_answer, reused_boundary_original_answer]

lemma boundary_outputs_valid :
    (∀ i : Fin 3, (![3, 5, 7] : Fin 3 → ℕ) i < literalBoundaryProgram.length) ∧
    (∀ i : Fin 3, (![6, 3, 4] : Fin 3 → ℕ) i < reusedBoundaryProgram.length) := by decide +kernel

/-- **GAC2:two-cell-three-output-programs**
(matched exact programs for all three native component outputs). -/
@[ledger "GAC2:two-cell-three-output-programs"]
theorem programsLaw : Statement.programsLaw := by
  exact ⟨two_cell_program_costs,
    literal_boundary_original_answer,
    reused_boundary_original_answer,
    matched_boundary_programs,
    boundary_outputs_valid⟩

/-! ## Non-vacuity -/
example : programOutput reusedBoundaryProgram ![6, 3, 4] ![-1, 3, 4 / 101] = ![2, 6 / 101, 2 /
  101] := by
  decide +kernel

end Artform.Scores.GravityBridge.Native.GreenComposition
