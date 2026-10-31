import ArtformScores.GravityBridge.Native.R7Blocks.Complete
import ArtformScores.GravityBridge.Realization
import ArtformScores.GravityBridge.Native.TemporalWitness

/-! # Artform visible closure and complete image invariance -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def blockRealization (K : Y →L[ℝ] Z) : Realization Y (Y × Z) where
  embed := graphMap K
  read := Prod.fst
  recover := fun _ => rfl

end Artform.Scores.GravityBridge.Native.R7Blocks
