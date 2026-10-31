import ArtformScores.GravityBridge.Native.CoordinateSymbol.CompanionDefs

/-! # Actual coordinate quartic bound to the complete companion -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement

open Matrix
open SlowCompanion

/-- **GAC2:native-quartic-companion-binding**
(actual coordinate quartic bound to the complete companion). -/
@[ledger "GAC2:native-quartic-companion-binding"]
def companionLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (j z : K) (k : Fin 3 → K) (_hj : j ^ 2 = -1),
    coordinatePolynomial (nativeEndCoefficients j k) z =
      Matrix.toLin' (nativeUpperSymbol (timeMomentum j z k))) ∧
    (∀ (j z : K) (k : Fin 3 → K) (b : Fin 4 → Vec4 (K := K))
    (_hj : j ^ 2 = -1) (_hR : spatialRadius k ≠ 0)
    (_hd : simpleDiscriminant (componentSquares (timeMomentum j z k)) (timeMomentum j z k) ≠ 0),
    z • nativeCompanionInverse j z k b-
      coordinateStep (nativeEndCoefficients j k) (Matrix.toLin' (leadingCoordinateInverse k))
        (nativeCompanionInverse j z k b) = b) ∧
    (∀ (j z : K) (k : Fin 3 → K)
    (x b : Fin 4 → Vec4 (K := K)) (_hj : j ^ 2 = -1) (_hR : spatialRadius k ≠ 0)
    (_hd : simpleDiscriminant (componentSquares (timeMomentum j z k)) (timeMomentum j z k) ≠ 0)
    (_hx : z • x - coordinateStep (nativeEndCoefficients j k)
      (Matrix.toLin' (leadingCoordinateInverse k)) x = b),
    x = nativeCompanionInverse j z k b)

end Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement
