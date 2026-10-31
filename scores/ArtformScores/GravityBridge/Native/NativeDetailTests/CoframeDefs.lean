import ArtformScores.GravityBridge.Native.NativeDetailTests.SourceBranch

/-! # Connection detail source leaves the complete coframe covector -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



noncomputable def nativeCoframeDensity (u r : ℝ) : ℝ := nativeSplitAction 1 u r 0

end Artform.Scores.GravityBridge.Native.NativeDetailTests
