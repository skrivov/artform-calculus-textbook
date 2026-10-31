import ArtformScores.GravityBridge.Native.CoordinateSymbol.PairedConnectionStatements

/-! # Original lower connection response on an angular-zero ray -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix



open Matrix

lemma paired_original_TT : pairedTT.transpose = pairedTT ∧ Matrix.trace pairedTT = 0 ∧
    pairedTT *ᵥ ![3, 3, 0] = 0 ∧ TTCoordinates.frobeniusSquare pairedTT = 2 := by
  constructor
  · ext i l; fin_cases i <;> fin_cases l <;> norm_num [pairedTT, Matrix.transpose_apply]
  constructor
  · norm_num [Matrix.trace, pairedTT, Fin.sum_univ_succ]
  constructor
  · ext i; fin_cases i <;> norm_num [pairedTT, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [TTCoordinates.frobeniusSquare, pairedTT, Fin.sum_univ_succ]

lemma paired_temporal_force :
    Artform.Scores.GravityBridge.Native.temporalSymbol ![3, 3, 0] pairedTT = -27 / 101 := by
  norm_num [Artform.Scores.GravityBridge.Native.temporalSymbol,
    Artform.Scores.GravityBridge.Native.rhoSquared,
    Artform.Scores.GravityBridge.Native.diagonalContraction, pairedTT, Fin.sum_univ_succ]

lemma psi_zero_connection_return :
    (-2 / 101 : ℚ) • (Retrospective.polynomialInverse (1 / 101) *ᵥ
      connectionSource (9 / 4)) = ![0, -9 / 206, 9 / 206] ∧
    (-2 / 101 : ℚ) • (Retrospective.polynomialInverse (1 / 101) *ᵥ
      connectionSource (9 / 4)) - Retrospective.curvatureOnlyPreparation (1 / 101) (9 / 4) =
      ![0, 9 / 10403, -9 / 10403] := by
  rw [Retrospective.first_contact_curvature_error, Retrospective.full_first_contact]
  constructor <;> ext i <;> fin_cases i <;> norm_num [connectionSource]

/-- **GAC2:native-angular-zero-connection-return**
(original lower connection response on an angular-zero ray). -/
@[ledger "GAC2:native-angular-zero-connection-return"]
theorem pairedConnectionLaw : Statement.pairedConnectionLaw := by
  exact ⟨paired_original_TT,
    paired_temporal_force,
    psi_zero_connection_return⟩

/-! ## Non-vacuity -/
example : ((-2 / 101 : ℚ) • (Retrospective.polynomialInverse (1 / 101) *ᵥ
    connectionSource (9 / 4))) 1 ≠ 0 := by
  rw [psi_zero_connection_return.1]; norm_num

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
