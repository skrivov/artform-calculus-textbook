import ArtformScores.GravityBridge.Native.TTCross.Source

/-! # Original paired-axis TT graph with its complete preparation -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

def pairedTTStep (a : K) (u : Fin 2 → K) : Fin 2 → K := ![u 1, -2 * a ^ 2 * u 0]

def preparedJet (a : K) (u : Fin 2 → K) : Fin 4 → K :=
  ![-u 1 / (2 * a ^ 2), u 0, u 1, -2 * a ^ 2 * u 0]

def forcedJetStep (a : K) (u : Fin 2 → K) (x : Fin 4 → K) : Fin 4 → K :=
  ![x 1, x 2, x 3, a ^ 2 * x 2 + 2 * a ^ 4 * x 0 - 2 * a ^ 2 * u 1]

end Artform.Scores.GravityBridge.Native.TTCross
