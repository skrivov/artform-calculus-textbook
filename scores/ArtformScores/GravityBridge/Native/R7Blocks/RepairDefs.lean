import ArtformScores.GravityBridge.Native.R7Blocks.Complete
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Ring.Units

/-! # The graph gap and whole-trace head normalization -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

noncomputable def graphGap (a d : ℝ) : ℝ := Real.sqrt (1 + d / (2 * a)) - 1

end Artform.Scores.GravityBridge.Native.R7Blocks
