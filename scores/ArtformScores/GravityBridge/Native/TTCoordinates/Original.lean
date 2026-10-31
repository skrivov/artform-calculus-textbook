import ArtformScores.GravityBridge.Native.TTCoordinates.OriginalStatements

/-! # The complete original TT plane and temporal witness -/

namespace Artform.Scores.GravityBridge.Native.TTCoordinates

open Matrix



open Matrix

lemma original_dyad_polarization : dyadPolarization = polarization := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [dyadPolarization, nativeU, nativeV, polarization]

lemma original_full_tensor_norm : frobeniusSquare polarization = 2 := by
  norm_num [frobeniusSquare, polarization, Fin.sum_univ_succ]

lemma parametric_TT_properties (x y : ℚ) :
    (parametricTT x y).transpose = parametricTT x y ∧ trace (parametricTT x y) = 0 ∧
    parametricTT x y *ᵥ momentum = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · norm_num [parametricTT, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;> norm_num [parametricTT, momentum, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

lemma complete_native_TT_parameterization (q : Matrix (Fin 3) (Fin 3) ℚ)
    (hs : q.transpose = q) (ht : trace q = 0) (hk : q *ᵥ momentum = 0) :
    q = parametricTT (q 0 0) (q 1 1) := by
  have hs10 : q 1 0 = q 0 1 := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℚ => m 0 1) hs
  have hs20 : q 2 0 = q 0 2 := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℚ => m 0 2) hs
  have hs21 : q 2 1 = q 1 2 := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℚ => m 1 2) hs
  have h0:=congrFun hk 0
  have h1:=congrFun hk 1
  have h2:=congrFun hk 2
  norm_num [momentum, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
  rw [hs10] at h1
  rw [hs20, hs21] at h2
  have htr : q 0 0 + q 1 1 + q 2 2 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, add_assoc] using ht
  have hz : q 2 2 = -q 0 0 - q 1 1 := by linear_combination htr
  have ha : q 0 1 = -(10 * q 0 0 + 13 * q 1 1) / 4 := by
    linear_combination (1 / 4 : ℚ) * h0 + (1 / 2 : ℚ) * h1 - (3 / 4 : ℚ) * h2 + (9 / 4 : ℚ) * htr
  have hb : q 0 2 = (8 * q 0 0 + 13 * q 1 1) / 6 := by
    linear_combination (1 / 3 : ℚ) * h0 - (2 / 3 : ℚ) * ha
  have hc : q 1 2 = (10 * q 0 0 + 5 * q 1 1) / 12 := by
    linear_combination (1 / 3 : ℚ) * h1 - (1 / 3 : ℚ) * ha
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact ha
  · exact hb
  · exact hs10.trans ha
  · rfl
  · exact hc
  · exact hs20.trans hb
  · exact hs21.trans hc
  · exact hz

lemma original_forcing_two_coordinates (q : Matrix (Fin 3) (Fin 3) ℚ)
    (ht : trace q = 0) : temporalSymbol momentum q = (14 / 101 : ℚ) * q 0 0 + (7 / 101 : ℚ) * q
      1 1 := by
  have htr : q 0 0 + q 1 1 + q 2 2 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, add_assoc] using ht
  norm_num [temporalSymbol, rhoSquared, diagonalContraction, momentum, Fin.sum_univ_succ]
  linear_combination (-21 / 101 : ℚ) * htr

lemma original_witness_recovered :
    polarization = parametricTT (47 / 70) (-22 / 70) ∧
    temporalSymbol momentum dyadPolarization = 36 / 505 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [polarization, parametricTT]
  · rw [original_dyad_polarization]
    exact temporalWitness.2.2.2.2.2.1

/-- **GAC2:original-native-tt-plane**
(the complete original tt plane and temporal witness). -/
@[ledger "GAC2:original-native-tt-plane"]
theorem originalLaw : Statement.originalLaw := by
  exact ⟨original_dyad_polarization,
    original_full_tensor_norm,
    parametric_TT_properties,
    complete_native_TT_parameterization,
    original_forcing_two_coordinates,
    original_witness_recovered⟩

/-! ## Non-vacuity -/

example : temporalSymbol momentum (parametricTT 1 0) = 14 / 101 ∧
    temporalSymbol momentum (parametricTT 0 1) = 7 / 101 := by
  constructor
  · rw [original_forcing_two_coordinates _ (parametric_TT_properties 1 0).2.1]
    norm_num [parametricTT]
  · rw [original_forcing_two_coordinates _ (parametric_TT_properties 0 1).2.1]
    norm_num [parametricTT]

end Artform.Scores.GravityBridge.Native.TTCoordinates
