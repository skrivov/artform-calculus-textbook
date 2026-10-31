import ArtformScores.NonabelianGravity.QuantumSliceData

/-! # Exact kernel replay of native Schur certificate data -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.QuantumComposition

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
-- Finite rational native Schur identities are checked row by row in the kernel.
lemma left_schur_solve :
    leftA * leftP = crossB := by
  funext i
  fin_cases i <;> decide +kernel

end Artform.Scores.NonabelianGravity.QuantumComposition
