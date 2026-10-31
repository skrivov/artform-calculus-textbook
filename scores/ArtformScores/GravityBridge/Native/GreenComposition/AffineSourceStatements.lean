import ArtformScores.GravityBridge.Native.GreenComposition.AffineSourceDefs

/-! # Affine boundary composition retains independent source contacts -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition.Statement

open scoped BigOperators

/-- **GAC2:source-complete-affine-boundary-composition**
(affine boundary composition retains independent source contacts). -/
@[ledger "GAC2:source-complete-affine-boundary-composition"]
def affineSourceLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (c a b j pin pout : K) (_hc : c ≠ 0),
    boundaryStep c j (a, pin) = (b, pout) ↔
      pin = inputMomentum c a b j ∧ pout = outputMomentum c a b j) ∧
    (∀ (c j l : K) (x : K × K),
    boundaryStep c l (boundaryStep c j x) =
      (x.1 + (2 * x.2 - (3 * j + l) / 2) / c, x.2 - j - l)) ∧
    (∀ (c a m b j l : K) (_hc : c ≠ 0),
    sourceEffective c a m j + sourceEffective c m b l =
      composeEffective c a b j l + c * (m - composeMiddle c a b j l) ^ 2) ∧
    (∀ (c a m b j l : K) (_hc : c ≠ 0),
    outputMomentum c a m j = inputMomentum c m b l ↔ m = composeMiddle c a b j l) ∧
    (composeEffective (1 / 101 : ℚ) 0 4 (2 / 101) (4 / 101) ≠ composeEffective (1 / 101 : ℚ) 0 4
      (6 / 101) 0)

end Artform.Scores.GravityBridge.Native.GreenComposition.Statement
