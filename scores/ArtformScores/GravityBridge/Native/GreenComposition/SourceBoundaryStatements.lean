import ArtformScores.GravityBridge.Native.GreenComposition.SourceBoundaryDefs

/-! # Full source and endpoint covector of the solved two-cell contribution -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition.Statement

open scoped BigOperators

/-- **GAC2:two-cell-complete-source-covector**
(full source and endpoint covector of the solved two-cell contribution). -/
@[ledger "GAC2:two-cell-complete-source-covector"]
def sourceBoundaryLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (c a m b j : K) (_hc : c ≠ 0),
    sourceAction c a m b j = sourceEffective c a b j + 2 * c * (m - sourceMiddle c a b j) ^ 2) ∧
    (∀ (c a m b j : K) (_hc : c ≠ 0),
    2 * c * (m - a) - 2 * c * (b - m) = j ↔ m = sourceMiddle c a b j) ∧
    (∀ (c a b j da db dj e : K) (_hc : c ≠ 0),
    sourceEffective c (a + e * da) (b + e * db) (j + e * dj) = sourceEffective c a b j +
      e * (-inputMomentum c a b j * da + outputMomentum c a b j * db - sourceMiddle c a b j * dj) +
      e ^ 2 * (c / 2 * (db - da) ^ 2 - dj * (da + db) / 2 - dj ^ 2 / (8 * c))) ∧
    (∀ (a m b j : ℚ),
    sourceAction (1 / 101) a m b j = twoCellTorsion a m b j ∧
    sourceMiddle (1 / 101) a b j = twoCellMiddle a b j ∧
    sourceEffective (1 / 101) a b j = twoCellEffective a b j) ∧
    (sourceMiddle (1 / 101 : ℚ) (-1) 3 (4 / 101) = 2 ∧
    inputMomentum (1 / 101 : ℚ) (-1) 3 (4 / 101) = 6 / 101 ∧
    outputMomentum (1 / 101 : ℚ) (-1) 3 (4 / 101) = 2 / 101 ∧
    sourceEffective (1 / 101 : ℚ) (-1) 3 (4 / 101) = 2 / 101)

end Artform.Scores.GravityBridge.Native.GreenComposition.Statement
