import ArtformScores.GravityBridge.Native.TTCross.Source
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Source-driven response with all four zero initial coordinate jets -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40



noncomputable def zeroPreparedJet (a l t : ℝ) : Fin 5 → ℝ :=
  ![(-3 * Real.cos (l * t) - Real.cosh (l * t) + 4 * Real.cos (a * t)) / (6 * a ^ 2),
    (3 * l * Real.sin (l * t) - l * Real.sinh (l * t) - 4 * a * Real.sin (a * t)) / (6 * a ^ 2),
    (3 * l ^ 2 * Real.cos (l * t) - l ^ 2 * Real.cosh (l * t) - 4 * a ^ 2 * Real.cos (a * t)) /
      (6 * a ^ 2),
    (-3 * l ^ 3 * Real.sin (l * t) - l ^ 3 * Real.sinh (l * t) + 4 * a ^ 3 * Real.sin (a * t)) /
      (6 * a ^ 2),
    (-3 * l ^ 4 * Real.cos (l * t) - l ^ 4 * Real.cosh (l * t) + 4 * a ^ 4 * Real.cos (a * t)) /
      (6 * a ^ 2)]

end Artform.Scores.GravityBridge.Native.TTCross
