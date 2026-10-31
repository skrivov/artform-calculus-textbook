import ArtformScores.GravityBridge.Native.GreenComposition.SusceptibilityDefs

/-! # Held-out source susceptibility and mixed boundary contacts -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition.Statement

open scoped BigOperators

/-- **GAC2:heldout-source-boundary-susceptibility**
(held-out source susceptibility and mixed boundary contacts). -/
@[ledger "GAC2:heldout-source-boundary-susceptibility"]
def susceptibilityLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (c a b j dj : K) (_hc : c ≠ 0),
    sourceMiddle c a b (j + dj) - sourceMiddle c a b j = dj / (4 * c) ∧
    sourceEffective c a b (j + dj) - sourceEffective c a b j =
      -sourceMiddle c a b j * dj - dj ^ 2 / (8 * c)) ∧
    (∀ (c a b j da db dj : K) (_hc : c ≠ 0),
    sourceEffective c (a + da) (b + db) (j + dj) - sourceEffective c (a + da) (b + db) j-
      sourceEffective c a b (j + dj) + sourceEffective c a b j = -dj * (da + db) / 2) ∧
    (∀ (c a b j : K) (_hc : c ≠ 0),
    sourceMiddle c a b j = (a + b) / 2 ↔ j = 0) ∧
    (sourceMiddle (1 / 101 : ℚ) (-1) 3 (5 / 101) - sourceMiddle (1 / 101) (-1) 3 (4 / 101) = 1 / 4 ∧
    sourceEffective (1 / 101 : ℚ) 0 5 (5 / 101) - sourceEffective (1 / 101) 0 5 (4 / 101)-
      sourceEffective (1 / 101) (-1) 3 (5 / 101) + sourceEffective (1 / 101) (-1) 3 (4 / 101) =
        -3 / 202)

end Artform.Scores.GravityBridge.Native.GreenComposition.Statement
