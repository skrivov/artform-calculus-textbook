import ArtformScores.GravityBridge.Native.R7Blocks.Complete

/-! # Complete Riccati recentering and quadratic feedback -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def linearizedRiccati (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A22 : Z →L[ℝ] Z) (K D : Y →L[ℝ] Z) : Y →L[ℝ] Z :=
  (A22 - K.comp A12).comp D - D.comp (A11 + A12.comp K)

end Artform.Scores.GravityBridge.Native.R7Blocks
