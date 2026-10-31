import ArtformScores.GravityBridge.Native.CoordinateSymbol.Leading
import ArtformScores.GravityBridge.Native.SlowCompanion.Resolvent

/-! # Actual coordinate quartic bound to the complete companion -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix
open SlowCompanion

variable {K : Type*} [Field K] [CharZero K]

def nativeEndCoefficients (j : K) (k : Fin 3 → K) : Fin 5 → Module.End K (Vec4 (K := K)) :=
  fun n => Matrix.toLin' (nativeUpperCoefficients j k n)

def nativeCompanionInverse (j z : K) (k : Fin 3 → K) (b : Fin 4 → Vec4 (K := K)) :
    Fin 4 → Vec4 (K := K) :=
  companionResolvent (nativeEndCoefficients j k)
    (Matrix.toLin' (nativeCoordinateInverse (timeMomentum j z k))) z b

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
