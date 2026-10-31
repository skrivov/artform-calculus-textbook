import ArtformScores.GravityBridge.Native.TTCross.ZeroResponseDefs

/-! # Source-driven response with all four zero initial coordinate jets -/

namespace Artform.Scores.GravityBridge.Native.TTCross.Statement

open Matrix CoordinateSymbol Full40

/-- **GAC2:native-tt-zero-preparation-response**
(source-driven response with all four zero initial coordinate jets). -/
@[ledger "GAC2:native-tt-zero-preparation-response"]
def zeroResponseLaw : Prop :=
    (∀ (a l t : ℝ),
    HasDerivAt (fun s => zeroPreparedJet a l s 0) (zeroPreparedJet a l t 1) t ∧
    HasDerivAt (fun s => zeroPreparedJet a l s 1) (zeroPreparedJet a l t 2) t ∧
    HasDerivAt (fun s => zeroPreparedJet a l s 2) (zeroPreparedJet a l t 3) t ∧
    HasDerivAt (fun s => zeroPreparedJet a l s 3) (zeroPreparedJet a l t 4) t) ∧
    (∀ (a l : ℝ) (_hl : l ^ 2 = 2 * a ^ 2),
    zeroPreparedJet a l 0 0 = 0 ∧ zeroPreparedJet a l 0 1 = 0 ∧
    zeroPreparedJet a l 0 2 = 0 ∧ zeroPreparedJet a l 0 3 = 0) ∧
    (∀ (a l t : ℝ) (_ha : a ≠ 0) (_hl : l ^ 2 = 2 * a ^ 2),
    zeroPreparedJet a l t 4 - a ^ 2 * zeroPreparedJet a l t 2-
      2 * a ^ 4 * zeroPreparedJet a l t 0 = -2 * a ^ 2 * Real.cos (l * t)) ∧
    (∀ (a l t : ℝ) (_ha : a ≠ 0),
    zeroPreparedJet a l t 0 =
      (-3 * Real.cos (l * t) + 4 * Real.cos (a * t)) / (6 * a ^ 2) - Real.cosh (l * t) / (6 * a
        ^ 2) ∧
      -(1 / (6 * a ^ 2)) ≠ 0)

end Artform.Scores.GravityBridge.Native.TTCross.Statement
