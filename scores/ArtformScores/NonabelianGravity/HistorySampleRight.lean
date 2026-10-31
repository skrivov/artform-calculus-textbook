import ArtformScores.NonabelianGravity.HistorySampleData

/-! # Kernel check of the emitted native three-cell certificate -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
-- All80 owned coordinates remain in this exact certificate identity.
lemma sample_right : sampleForward * sampleBackward = 1 := by
  funext i
  rcases i with ⟨t, k⟩
  fin_cases t <;> fin_cases k <;> decide +kernel

end Artform.Scores.NonabelianGravity.HistoryElimination
