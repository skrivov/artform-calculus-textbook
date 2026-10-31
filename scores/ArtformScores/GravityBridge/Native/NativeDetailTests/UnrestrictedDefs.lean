import ArtformScores.GravityBridge.Native.NativeDetailTests.Coframe
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Unrestricted positive real weight is not a finite normalization -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



noncomputable def positiveRealWeight (b u r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-nativeSplitAction b u r 0))

end Artform.Scores.GravityBridge.Native.NativeDetailTests
