import ArtformScores.GravityBridge.Native.CoordinateSymbol.Band

/-! # R7 band and R8 angular exceptional domains -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix



def spatialFourth (k : Fin 3 → ℝ) : ℝ := k 0 ^ 4 + k 1 ^ 4 + k 2 ^ 4

noncomputable def angularPsi (k : Fin 3 → ℝ) : ℝ := spatialFourth k - cubicMoment k ^ 2 /
  radiusSquared k

def angularSquares (k : Fin 3 → ℝ) : ℝ :=
  k 0 ^ 2 * k 1 ^ 2 * (k 0 - k 1) ^ 2 + k 0 ^ 2 * k 2 ^ 2 * (k 0 - k 2) ^ 2 +
    k 1 ^ 2 * k 2 ^ 2 * (k 1 - k 2) ^ 2

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
