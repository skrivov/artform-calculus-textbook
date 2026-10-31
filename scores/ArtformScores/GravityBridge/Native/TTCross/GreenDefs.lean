import ArtformScores.GravityBridge.Native.TTCross.Prepared

/-! # Full four-jet scalar current and its prepared pullback -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

def scalarGreen (a : K) (x y : Fin 4 → K) : K :=
  x 0 * y 3 - x 1 * y 2 + x 2 * y 1 - x 3 * y 0 - a ^ 2 * (x 0 * y 1 - x 1 * y 0)

def scalarRow (a : K) (x : Fin 5 → K) : K := x 4 - a ^ 2 * x 2 - 2 * a ^ 4 * x 0

def firstFour (x : Fin 5 → K) : Fin 4 → K := fun i => x i.castSucc

def nextFour (x : Fin 5 → K) : Fin 4 → K := fun i => x i.succ

end Artform.Scores.GravityBridge.Native.TTCross
