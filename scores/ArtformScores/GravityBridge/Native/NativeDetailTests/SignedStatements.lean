import ArtformScores.GravityBridge.Native.NativeDetailTests.SignedDefs

/-! # Signed native rapidity can remove the real stationary branch -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal

/-- **GAC2:native-negative-detail-discriminant**
(signed native rapidity can remove the real stationary branch). -/
@[ledger "GAC2:native-negative-detail-discriminant"]
def signedLaw : Prop :=
    (∀ (A B C S : ℝ)
    (_hD : A ^ 2 - B ^ 2 < 0) (_hL : C ^ 2 - S ^ 2 = 1),
    A * S + B * C ≠ 0) ∧
    (detailD (Real.cosh (Real.log (201 / 202))) (Real.sinh (Real.log (201 / 202))) =
      -151 / 83250381402) ∧
    (∀ (b : ℝ) (_hb : b ≠ 0) (r : ℝ),
    nativeSplitFirst b (Real.log (201 / 202)) r 0 ≠ 0) ∧
    (0 < (201 / 202 : ℝ) ∧ (201 / 202 : ℝ) < 1 ∧
    Real.log (201 / 202) < 0)

end Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement
