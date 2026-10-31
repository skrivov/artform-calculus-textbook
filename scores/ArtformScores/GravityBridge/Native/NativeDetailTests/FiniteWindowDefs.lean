import ArtformScores.GravityBridge.Native.NativeDetailTests.Unrestricted

/-! # Bounded native detail interval has explicit finite positive mass -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



noncomputable def boundedWeightCeiling (b u L : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (b * detailRoot u * Real.cosh L - (1 / 101 : ℝ) * b))

end Artform.Scores.GravityBridge.Native.NativeDetailTests
