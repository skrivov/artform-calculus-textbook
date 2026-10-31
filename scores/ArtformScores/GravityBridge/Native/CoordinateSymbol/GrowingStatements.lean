import ArtformScores.GravityBridge.Native.CoordinateSymbol.GrowingDefs

/-! # Actual native coordinate column and its extra real root -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement

open Matrix

/-- **GAC2:native-coordinate-extra-real-root**
(actual native coordinate column and its extra real root). -/
@[ledger "GAC2:native-coordinate-extra-real-root"]
def growingLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (j z a : K) (_hj : j ^ 2 = -1),
    simpleDiscriminant (componentSquares (timeMomentum j z ![a, -a, 0]))
      (timeMomentum j z ![a, -a, 0]) = -(a ^ 2 / 2) * (z ^ 2 - 2 * a ^ 2) * (z ^ 2 + a ^ 2)) ∧
    (∀ (j z a : K) (_hj : j ^ 2 = -1),
    nativeUpperSymbol (timeMomentum j z ![a, -a, 0]) *ᵥ ![0, 0, 0, 1] =
      (-(1 / 101 : K) * (9999 / 9991) * a ^ 2 * (z ^ 2 - 2 * a ^ 2) * (z ^ 2 + a ^ 2)) • ![0, 0,
        0, 1]) ∧
    (∀ (j z a : K) (_hj : j ^ 2 = -1) (_hz : z ^ 2 = 2 * a ^ 2),
    nativeUpperSymbol (timeMomentum j z ![a, -a, 0]) *ᵥ ![0, 0, 0, 1] = 0)

end Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement
