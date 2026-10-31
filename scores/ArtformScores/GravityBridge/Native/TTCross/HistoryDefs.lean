import ArtformScores.GravityBridge.Native.TTCross.ZeroResponse
import ArtformScores.GravityBridge.Native.TTCross.Green

/-! # Bounded native coordinate history does not determine preparation -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40



noncomputable def boundedHomogeneousJet (a t : ℝ) : Fin 5 → ℝ :=
  ![Real.cos (a * t), -a * Real.sin (a * t), -a ^ 2 * Real.cos (a * t),
    a ^ 3 * Real.sin (a * t), a ^ 4 * Real.cos (a * t)]

end Artform.Scores.GravityBridge.Native.TTCross
