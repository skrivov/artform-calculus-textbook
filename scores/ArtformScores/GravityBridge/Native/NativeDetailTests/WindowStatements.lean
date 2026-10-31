import ArtformScores.GravityBridge.Native.NativeDetailTests.WindowDefs

/-! # Exact native source window for both child rapidities -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal

/-- **GAC2:native-source-rapidity-window**
(exact native source window for both child rapidities). -/
@[ledger "GAC2:native-source-rapidity-window"]
def windowLaw : Prop :=
    (∀ (b u : ℝ),
    nativeSplitFirst b u (-u) 0 = 2 * b * (Real.sinh u) ^ 2 ∧
    nativeSplitFirst b u u 0 = -2 * b * (Real.sinh u) ^ 2 - (2 / 101 : ℝ) * b * Real.sinh u *
      Real.cosh u) ∧
    (∀ (b u r j : ℝ) (_hb : 0 < b) (_hu : 0 < u)
    (_hz : nativeSplitFirst b u r j = 0),
    (-u < r ∧ r < u) ↔
      (-2 * b * (Real.sinh u) ^ 2 - (2 / 101 : ℝ) * b * Real.sinh u * Real.cosh u < j ∧
        j < 2 * b * (Real.sinh u) ^ 2)) ∧
    (∀ (b u j : ℝ) (_hb : 0 < b) (_hu : 0 < u)
    (_hj : -2 * b * (Real.sinh u) ^ 2 - (2 / 101 : ℝ) * b * Real.sinh u * Real.cosh u < j ∧
      j < 2 * b * (Real.sinh u) ^ 2),
    ∃ r : ℝ, nativeSplitFirst b u r j = 0 ∧
      0 < u + r ∧ u + r < 2 * u ∧ 0 < u - r ∧ u - r < 2 * u)

end Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement
