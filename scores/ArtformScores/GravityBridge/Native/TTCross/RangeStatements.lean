import ArtformScores.GravityBridge.Native.TTCross.RangeDefs

/-! # Actual TT source range and failure of global preparation bounds -/

namespace Artform.Scores.GravityBridge.Native.TTCross.Statement

open Matrix CoordinateSymbol Full40

/-- **GAC2:native-tt-source-range-budget**
(actual tt source range and failure of global preparation bounds). -/
@[ledger "GAC2:native-tt-source-range-budget"]
def rangeLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (a r : K) (_ha : a ≠ 0),
    actualCrossSource a (sourceVelocity a r) = r • ![0, 0, 0, 1]) ∧
    (∀ (a v : K) (_ha : a ≠ 0),
    actualCrossSource a v = 0 ↔ v = 0) ∧
    ((∑ i : Fin 4, ∑ l : Fin 4, (crossMetric (K := ℚ) i l) ^ 2) = 4) ∧
    (∀ (a : ℝ),
    preparedJet a ![0, 1] 0 = -1 / (2 * a ^ 2)) ∧
    (∀ (B : ℝ) (_hB : 0 ≤ B),
    ∃ a : ℝ, a ≠ 0 ∧ B + 1 ≤ |preparedJet a ![0, 1] 0|)

end Artform.Scores.GravityBridge.Native.TTCross.Statement
