import ArtformScores.GravityBridge.Native.TTCross.Prepared

/-! # Read inverse and explicit budget on the paired native band slice -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40



def pairedReadout (x : Fin 4 → ℝ) : Fin 2 → ℝ := ![x 1, x 2]

end Artform.Scores.GravityBridge.Native.TTCross
