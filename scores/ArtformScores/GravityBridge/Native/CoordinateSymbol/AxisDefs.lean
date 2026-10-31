import ArtformScores.GravityBridge.Native.CoordinateSymbol.Inverse

/-! # Axis branches retain the complete mixed numerator -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix

variable {K : Type*} [Field K] [CharZero K]

def mixedFaceSource (j : K) (p : Vec4 (K := K))
    (Q : Fin 4 → Fin 4 → Fin 4 → K) : Vec4 (K := K) := fun a =>
  (2 * j / 101) * signature a * (
    simpleFace (componentSquares p) p 0 1 * Q 0 1 a +
    simpleFace (componentSquares p) p 0 2 * Q 0 2 a +
    simpleFace (componentSquares p) p 0 3 * Q 0 3 a +
    simpleFace (componentSquares p) p 1 2 * Q 1 2 a +
    simpleFace (componentSquares p) p 1 3 * Q 1 3 a +
    simpleFace (componentSquares p) p 2 3 * Q 2 3 a)

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
