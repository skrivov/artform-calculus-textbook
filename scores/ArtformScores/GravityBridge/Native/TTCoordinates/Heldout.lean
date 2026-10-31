import ArtformScores.GravityBridge.Native.TTCoordinates.HeldoutStatements

/-! # A second off-axis native temporal forcing test -/

namespace Artform.Scores.GravityBridge.Native.TTCoordinates

open Matrix



open Matrix

lemma heldout_dyad_identity : heldoutPolarization = heldoutDyad := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heldoutPolarization, heldoutDyad, heldoutU, heldoutV]

lemma heldout_original_TT_test :
    heldoutPolarization.transpose = heldoutPolarization ∧ trace heldoutPolarization = 0 ∧
    heldoutPolarization *ᵥ heldoutMomentum = 0 ∧
    (∑ i, ∑ j, (heldoutPolarization i j) ^ 2) = 2 ∧
    temporalSymbol heldoutMomentum heldoutPolarization = 59 / 505 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [heldoutPolarization]
  · norm_num [heldoutPolarization, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;> norm_num [heldoutPolarization, heldoutMomentum,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [heldoutPolarization, Fin.sum_univ_succ]
  · norm_num [heldoutPolarization, heldoutMomentum, temporalSymbol,
      rhoSquared, diagonalContraction, Fin.sum_univ_succ]

lemma heldout_trace_reduction (q : Matrix (Fin 3) (Fin 3) ℚ) (ht : trace q = 0) :
    temporalSymbol heldoutMomentum q = (63 / 202 : ℚ) * q 0 0 + (42 / 202 : ℚ) * q 1 1 := by
  have htr : q 0 0 + q 1 1 + q 2 2 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, add_assoc] using ht
  norm_num [temporalSymbol, rhoSquared, diagonalContraction, heldoutMomentum, Fin.sum_univ_succ]
  linear_combination (-42 / 101 : ℚ) * htr

lemma heldout_nonzero_native_witness : temporalSymbol heldoutMomentum heldoutPolarization≠0 := by
  rw [heldout_original_TT_test.2.2.2.2]
  norm_num

/-- **GAC2:heldout-native-tt-force**
(a second off-axis native temporal forcing test). -/
@[ledger "GAC2:heldout-native-tt-force"]
theorem heldoutLaw : Statement.heldoutLaw := by
  exact ⟨heldout_dyad_identity,
    heldout_original_TT_test,
    heldout_trace_reduction,
    heldout_nonzero_native_witness⟩

/-! ## Non-vacuity -/

example : heldoutMomentum≠momentum ∧ temporalSymbol heldoutMomentum heldoutPolarization≠0 := by
  constructor
  · intro h
    have hz := congrFun h 2
    norm_num [heldoutMomentum, momentum] at hz
  · exact heldout_nonzero_native_witness

end Artform.Scores.GravityBridge.Native.TTCoordinates
