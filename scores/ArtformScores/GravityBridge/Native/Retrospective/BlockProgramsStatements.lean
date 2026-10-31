import ArtformScores.GravityBridge.Native.Retrospective.BlockProgramsDefs
/-! # Verified exact arithmetic programs for the original native block -/
namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement
open Matrix
/-- **GAC2:verified-native-block-programs**
(verified exact arithmetic programs for the original native block). -/
@[ledger "GAC2:verified-native-block-programs"]
def blockProgramsLaw : Prop :=
    (validProgram 0 denseBlockProgram = true ∧
    validProgram 0 rankBlockProgram = true ∧
    scaleCount denseBlockProgram = 9 ∧ addCount denseBlockProgram = 6 ∧
    scaleCount rankBlockProgram = 4 ∧ addCount rankBlockProgram = 5) ∧
    (∀ (z : Fin 3 → ℚ),
    programOutput denseBlockProgram ![4, 9, 14] z =
      programOutput rankBlockProgram ![6, 7, 8] z) ∧
    (∀ (z : Fin 3 → ℚ),
    programOutput rankBlockProgram ![6, 7, 8] z = connectionBlock⁻¹ *ᵥ z) ∧
    (∀ (z : Fin 3 → ℚ),
    programOutput denseBlockProgram ![4, 9, 14] z = connectionBlock⁻¹ *ᵥ z) ∧
    ((∀ i : Fin 3, (![4, 9, 14] : Fin 3 → ℕ) i < denseBlockProgram.length) ∧
      (∀ i : Fin 3, (![6, 7, 8] : Fin 3 → ℕ) i < rankBlockProgram.length))
end Artform.Scores.GravityBridge.Native.Retrospective.Statement
