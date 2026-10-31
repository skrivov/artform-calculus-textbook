import ArtformScores.GravityBridge.Native.GreenComposition.Temporal
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Fourier reality and the actual temporal halo duty -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators



noncomputable def evenScalarSeed (k : ℝ) : ℂ := (Real.exp (-(k ^ 2)) : ℝ)

noncomputable def derivedVectorSeed (k : ℝ) : ℂ := Complex.I * (k : ℂ) * evenScalarSeed k

def haloLeft (n : ℤ) : ℚ := if n = 0 then 1 else 0

def haloRight (n : ℤ) : ℚ := if n = 2 then 1 else 0

end Artform.Scores.GravityBridge.Native.GreenComposition
