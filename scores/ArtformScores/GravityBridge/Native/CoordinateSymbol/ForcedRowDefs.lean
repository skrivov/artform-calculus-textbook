import ArtformScores.GravityBridge.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Native unit-row forcing with zero initial four-jet -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix



noncomputable def rowUnitScale : ℝ := -(101 : ℝ) * (9991 / 9999)

noncomputable def forcedRowJet (l t : ℝ) : Fin 5 → ℝ :=
  ![rowUnitScale * (Real.cosh (l * t) + 2 * Real.cos t - 3) / 6,
    rowUnitScale * (l * Real.sinh (l * t) - 2 * Real.sin t) / 6,
    rowUnitScale * (l ^ 2 * Real.cosh (l * t) - 2 * Real.cos t) / 6,
    rowUnitScale * (l ^ 3 * Real.sinh (l * t) + 2 * Real.sin t) / 6,
    rowUnitScale * (l ^ 4 * Real.cosh (l * t) + 2 * Real.cos t) / 6]

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
