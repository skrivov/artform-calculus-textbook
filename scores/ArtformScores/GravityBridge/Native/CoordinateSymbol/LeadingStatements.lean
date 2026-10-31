import ArtformScores.GravityBridge.Native.CoordinateSymbol.LeadingDefs

/-! # Complete native quartic and its leading inverse -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement

open Matrix

/-- **GAC2:native-quartic-leading-inverse**
(complete native quartic and its leading inverse). -/
@[ledger "GAC2:native-quartic-leading-inverse"]
def leadingLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (j z : K) (k : Fin 3 → K) (_hj : j ^ 2 = -1),
    nativeUpperSymbol (timeMomentum j z k) = matrixPolynomial (nativeUpperCoefficients j k) z ∧
    nativeUpperCoefficients j k 4 = leadingCoordinate k) ∧
    (∀ (k : Fin 3 → K) (_hR : spatialRadius k ≠ 0),
    leadingCoordinate k * leadingCoordinateInverse k = 1 ∧
    leadingCoordinateInverse k * leadingCoordinate k = 1)

end Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement
