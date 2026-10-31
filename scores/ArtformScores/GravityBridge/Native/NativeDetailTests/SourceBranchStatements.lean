import ArtformScores.GravityBridge.Native.NativeDetailTests.SourceBranchDefs

/-! # Every real source has one stationary native detail on the positive branch -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal

/-- **GAC2:native-global-source-detail**
(every real source has one stationary native detail on the positive branch). -/
@[ledger "GAC2:native-global-source-detail"]
def sourceBranchLaw : Prop :=
    (∀ (u : ℝ) (_hu : 0 < u),
    0 < detailRoot u) ∧
    (∀ (b u r : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    nativeSplitSecond b u r < 0) ∧
    (∀ (b u j : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    StrictAnti (fun r => nativeSplitFirst b u r j)) ∧
    (∀ (b u r r0 j : ℝ) (_hu : 0 < u)
    (_hc : Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u))
    (_hs : Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u)),
    nativeSplitFirst b u r j = -b * detailRoot u * Real.sinh (r - r0) - j ∧
    nativeSplitAction b u r j = (1 / 101 : ℝ) * b - b * detailRoot u * Real.cosh (r - r0) - j * r) ∧
    (∀ (b u j : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    ∃! r : ℝ, nativeSplitFirst b u r j = 0)

end Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement
