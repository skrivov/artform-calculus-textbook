import ArtformScores.GravityBridge.Native.CurvedSubdivision.MergeDefs

/-! # Corrected stationary native merge still differs from the parent -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement

open Matrix Full40

/-- **GAC2:native-stationary-merge-defect**
(corrected stationary native merge still differs from the parent). -/
@[ledger "GAC2:native-stationary-merge-defect"]
def mergeLaw : Prop :=
    (∀ (b u : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    ∃ r : ℝ, -u < r ∧ r < 0 ∧ nativeSplitFirst b u r 0 = 0 ∧
      0 < literalTwoChildAction b u r-
        fullOriginalCell 1 b 1 0 (Real.cosh (2 * u)) (Real.sinh (2 * u))) ∧
    (∀ (delta : ℝ) (_hd : 0 < delta),
    ∃ u r : ℝ, 0 < u ∧ 2 * u < delta ∧ 0 < u + r ∧ u + r < delta ∧
      0 < u - r ∧ u - r < delta ∧ nativeSplitFirst 1 u r 0 = 0 ∧
      0 < literalTwoChildAction 1 u r-
        fullOriginalCell 1 1 1 0 (Real.cosh (2 * u)) (Real.sinh (2 * u))) ∧
    (∀ (b c s : ℝ) (_hc : c ^ 2 - s ^ 2 = 1)
    (_hco : 1 < c) (_hs : 0 < s),
    (stationaryValue b c s + 2 * b * c * s) *
      ((1 / 101 : ℝ) + 2 * c * s + Real.sqrt (detailD c s)) = 4 * b * s ^ 4)

end Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement
