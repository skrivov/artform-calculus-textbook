import ArtformScores.GravityBridge.Native.NativeDetailTests.SourceBranch

/-! # Original source envelope retains its derivative and susceptibility -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



noncomputable def sourceSlope (b u j : ℝ) : ℝ :=
  -(Real.sqrt (1 + (j / (b * detailRoot u)) ^ 2))⁻¹ / (b * detailRoot u)

noncomputable def nativeEnvelope (b u r0 j : ℝ) : ℝ :=
  (1 / 101 : ℝ) * b - b * detailRoot u * Real.cosh (sourceRapidity b u r0 j - r0)-
    j * sourceRapidity b u r0 j

noncomputable def rawEnvelope (b u r0 j : ℝ) : ℝ :=
  (1 / 101 : ℝ) * b - b * detailRoot u * Real.cosh (sourceRapidity b u r0 j - r0)

end Artform.Scores.GravityBridge.Native.NativeDetailTests
