import ArtformScores.GravityBridge.Native.CoordinateSymbol.AxisDefs

/-! # Axis branches retain the complete mixed numerator -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement

open Matrix

/-- **GAC2:native-axis-complete-source-numerator**
(axis branches retain the complete mixed numerator). -/
@[ledger "GAC2:native-axis-complete-source-numerator"]
def axisLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (a : K),
    simpleFace (componentSquares (![a, a, 0, 0] : Vec4 (K := K))) ![a, a, 0, 0] = 0) ∧
    (∀ (a : K),
    nativeUpperSymbol (![a, a, 0, 0] : Vec4 (K := K)) = 0) ∧
    (∀ (j a : K) (Q : Fin 4 → Fin 4 → Fin 4 → K),
    mixedFaceSource j ![a, a, 0, 0] Q = 0) ∧
    (∀ (a : K),
    simpleDiscriminant (componentSquares (![-a, a, 0, 0] : Vec4 (K := K))) ![-a, a, 0, 0] = -a ^
      6) ∧
    (∀ (a : K) (_ha : a ≠ 0),
    nativeUpperSymbol (![-a, a, 0, 0] : Vec4 (K := K)) * nativeCoordinateInverse ![-a, a, 0, 0]
      = 1 ∧
    nativeCoordinateInverse (![-a, a, 0, 0] : Vec4 (K := K)) * nativeUpperSymbol ![-a, a, 0, 0] = 1)

end Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement
