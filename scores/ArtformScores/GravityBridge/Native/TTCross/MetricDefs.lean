import ArtformScores.GravityBridge.Native.TTCross.Prepared

/-! # Metric cost of the full paired-axis preparation -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

def preparedMetricCut (j a : K) (u : Fin 2 → K) : Matrix (Fin 4) (Fin 4) K :=
  let d := ![preparedJet a u 1, j * a * preparedJet a u 0, -j * a * preparedJet a u 0, 0]
  fun i l => (if l = 3 then d i else 0) + (if i = 3 then d l else 0)

end Artform.Scores.GravityBridge.Native.TTCross
