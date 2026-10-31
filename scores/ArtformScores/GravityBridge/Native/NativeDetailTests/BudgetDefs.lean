import ArtformScores.GravityBridge.Native.NativeDetailTests.SourceBranch
import ArtformScores.GravityBridge.Native.CurvedSubdivision.Merge

/-! # Small native value defect does not supply a derivative budget -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



noncomputable def effectiveMergeDefect (b u : ℝ) : ℝ :=
  stationaryValue b (Real.cosh u) (Real.sinh u) + b * Real.sinh (2 * u)

noncomputable def physicalSecondDifference (h u r : ℝ) : ℝ :=
  ((-2 * u) / h - 2 * (-(u + r) / h)) / (h / 2) ^ 2

end Artform.Scores.GravityBridge.Native.NativeDetailTests
