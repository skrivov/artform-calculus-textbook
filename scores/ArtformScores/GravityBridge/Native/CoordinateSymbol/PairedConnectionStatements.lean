import ArtformScores.GravityBridge.Native.CoordinateSymbol.PairedConnectionDefs

/-! # Original lower connection response on an angular-zero ray -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement

open Matrix

/-- **GAC2:native-angular-zero-connection-return**
(original lower connection response on an angular-zero ray). -/
@[ledger "GAC2:native-angular-zero-connection-return"]
def pairedConnectionLaw : Prop :=
    (pairedTT.transpose = pairedTT ∧ Matrix.trace pairedTT = 0 ∧
    pairedTT *ᵥ ![3, 3, 0] = 0 ∧ TTCoordinates.frobeniusSquare pairedTT = 2) ∧
    (Artform.Scores.GravityBridge.Native.temporalSymbol ![3, 3, 0] pairedTT = -27 / 101) ∧
    ((-2 / 101 : ℚ) • (Retrospective.polynomialInverse (1 / 101) *ᵥ
      connectionSource (9 / 4)) = ![0, -9 / 206, 9 / 206] ∧
    (-2 / 101 : ℚ) • (Retrospective.polynomialInverse (1 / 101) *ᵥ
      connectionSource (9 / 4)) - Retrospective.curvatureOnlyPreparation (1 / 101) (9 / 4) =
      ![0, 9 / 10403, -9 / 10403])

end Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement
