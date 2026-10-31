import ArtformScores.GravityBridge.Native.NativeDetailTests.CoframeDefs

/-! # Connection detail source leaves the complete coframe covector -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal

/-- **GAC2:native-all-detail-coframe-source**
(connection detail source leaves the complete coframe covector). -/
@[ledger "GAC2:native-all-detail-coframe-source"]
def coframeLaw : Prop :=
    (∀ (u r : ℝ) (_hu : 0 < u),
    nativeCoframeDensity u r < 0) ∧
    (∀ (b u r j : ℝ) (_hb : b ≠ 0),
    HasDerivAt (fun x => literalTwoChildAction x u r - j * r) (nativeCoframeDensity u r) b) ∧
    (∀ (b u r j : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    HasDerivAt (fun x => literalTwoChildAction x u r - j * r) (nativeCoframeDensity u r) b ∧
      nativeCoframeDensity u r < 0) ∧
    (∀ (b u r : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    nativeSplitAction b u r 0 < 0)

end Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement
