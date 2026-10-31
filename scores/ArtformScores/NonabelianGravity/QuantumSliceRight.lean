import ArtformScores.NonabelianGravity.QuantumSliceData

/-! # Exact kernel replay of native Schur certificate data -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.QuantumComposition

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
-- Finite rational native Schur identities are checked row by row in the kernel.
lemma right_congruence_data :
    rightForward.transpose * sliceData * rightForward = Matrix.diagonal rightDiagonal := by
  funext i
  rcases i with i | i <;> fin_cases i <;> decide +kernel

end Artform.Scores.NonabelianGravity.QuantumComposition
