import ArtformScores.GravityBridge.Native.TTCross.Source
import ArtformScores.GravityBridge.Native.TTCross.Green

/-! # Embed the actual paired source in all four coordinate rows -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

def rowCoefficients (a : K) : Fin 5 → K :=
  ![(2 / 101 : K) * (9999 / 9991) * a ^ 6, 0, (1 / 101 : K) * (9999 / 9991) * a ^ 4, 0,
    -(1 / 101 : K) * (9999 / 9991) * a ^ 2]

def fullCoordinateRow (j a : K) (x : Fin 5 → K) : Vec4 (K := K) :=
  ∑ r : Fin 5, (etaMatrix * nativeUpperCoefficients j ![a, -a, 0] r * etaMatrix) *ᵥ
    (x r • ![0, 0, 0, 1])

def actualCrossSource (a v : K) : Vec4 (K := K) :=
  (-(2 / 101 : K) * (9999 / 9991) * a ^ 4 * v) • ![0, 0, 0, 1]

end Artform.Scores.GravityBridge.Native.TTCross
