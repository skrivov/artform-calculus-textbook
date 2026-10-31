import ArtformScores.GravityBridge.Native.CurvedSubdivision.Detail
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Every real source has one stationary native detail on the positive branch -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



noncomputable def detailRoot (u : ℝ) : ℝ := Real.sqrt (detailD (Real.cosh u) (Real.sinh u))

noncomputable def sourceRapidity (b u r0 j : ℝ) : ℝ := r0 - Real.arsinh (j / (b * detailRoot u))

end Artform.Scores.GravityBridge.Native.NativeDetailTests
