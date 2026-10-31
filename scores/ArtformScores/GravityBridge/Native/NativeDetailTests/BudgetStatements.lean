import ArtformScores.GravityBridge.Native.NativeDetailTests.BudgetDefs

/-! # Small native value defect does not supply a derivative budget -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal

/-- **GAC2:native-stationary-value-trace-budget**
(small native value defect does not supply a derivative budget). -/
@[ledger "GAC2:native-stationary-value-trace-budget"]
def budgetLaw : Prop :=
    (∀ (b u : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    0 < effectiveMergeDefect b u ∧ effectiveMergeDefect b u < 202 * b * (Real.sinh u) ^ 4) ∧
    (∀ (u delta : ℝ) (_hu : 0 < u) (_hd : u ≤ delta),
    Real.sinh u ≤ u * Real.cosh delta) ∧
    (∀ (b u delta : ℝ) (_hb : 0 < b) (_hu : 0 < u)
    (_hd : u ≤ delta),
    0 < effectiveMergeDefect b u ∧
      effectiveMergeDefect b u < 202 * b * (Real.cosh delta) ^ 4 * u ^ 4) ∧
    (∀ (b h v delta : ℝ) (_hb : 0 < b) (_hh : 0 < h)
    (_hv : 0 < v) (_hd : h * v ≤ delta),
    0 < effectiveMergeDefect b (h * v) ∧
      effectiveMergeDefect b (h * v) < 202 * b * (Real.cosh delta) ^ 4 * h ^ 4 * v ^ 4) ∧
    (∀ (b u : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    ∃ r : ℝ, -u < r ∧ r < 0 ∧ HasDerivAt (literalTwoChildAction b u) 0 r ∧
      literalTwoChildAction b u r-
        fullOriginalCell 1 b 1 0 (Real.cosh (2 * u)) (Real.sinh (2 * u)) = effectiveMergeDefect
          b u) ∧
    (∀ (b u : ℝ),
    nativeSplitFirst b u (-u / 2) 0 = b * Real.sinh (u / 2) * (2 * Real.sinh u - (1 / 101 : ℝ))) ∧
    (∀ (b u r : ℝ)
    (_hb : 0 < b) (_hu : 0 < u) (_hs : 2 * Real.sinh u < (1 / 101 : ℝ))
    (_hr : nativeSplitFirst b u r 0 = 0),
    r < -u / 2) ∧
    (∀ (b h v r : ℝ)
    (_hb : 0 < b) (_hh : 0 < h) (_hv : 0 < v)
    (_hs : 2 * Real.sinh (h ^ 2 * v) < (1 / 101 : ℝ))
    (_hr : nativeSplitFirst b (h ^ 2 * v) r 0 = 0),
    4 * v / h < |physicalSecondDifference h (h ^ 2 * v) r|)

end Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement
