import ArtformScores.GravityBridge.Native.GreenComposition.ProgramsDefs

/-! # Matched exact programs for all three native component outputs -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition.Statement

open scoped BigOperators
open Matrix Retrospective

/-- **GAC2:two-cell-three-output-programs**
(matched exact programs for all three native component outputs). -/
@[ledger "GAC2:two-cell-three-output-programs"]
def programsLaw : Prop :=
    (validProgram 0 literalBoundaryProgram = true ∧ validProgram 0 reusedBoundaryProgram = true ∧
    scaleCount literalBoundaryProgram = 4 ∧ addCount literalBoundaryProgram = 4 ∧
    scaleCount reusedBoundaryProgram = 3 ∧ addCount reusedBoundaryProgram = 4) ∧
    (∀ (x : Fin 3 → ℚ),
    programOutput literalBoundaryProgram ![3, 5, 7] x =
      ![sourceMiddle (1 / 101) (x 0) (x 1) (x 2),
        inputMomentum (1 / 101) (x 0) (x 1) (x 2),
        outputMomentum (1 / 101) (x 0) (x 1) (x 2)]) ∧
    (∀ (x : Fin 3 → ℚ),
    programOutput reusedBoundaryProgram ![6, 3, 4] x =
      ![sourceMiddle (1 / 101) (x 0) (x 1) (x 2),
        inputMomentum (1 / 101) (x 0) (x 1) (x 2),
        outputMomentum (1 / 101) (x 0) (x 1) (x 2)]) ∧
    (∀ (x : Fin 3 → ℚ),
    programOutput literalBoundaryProgram ![3, 5, 7] x = programOutput reusedBoundaryProgram ![6,
      3, 4] x) ∧
    ((∀ i : Fin 3, (![3, 5, 7] : Fin 3 → ℕ) i < literalBoundaryProgram.length) ∧
    (∀ i : Fin 3, (![6, 3, 4] : Fin 3 → ℕ) i < reusedBoundaryProgram.length))

end Artform.Scores.GravityBridge.Native.GreenComposition.Statement
