import ArtformScores.GravityBridge.Native.CurvedSubdivision.SeamDefs

/-! # A fused coarse link does not fix the fine seam -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement

open Matrix Full40

/-- **GAC2:native-curved-seam-detail**
(a fused coarse link does not fix the fine seam). -/
@[ledger "GAC2:native-curved-seam-detail"]
def seamLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (q : K),
    qC q + qS q = q) ∧
    (Function.Injective (rationalBoost (K := K))) ∧
    (∀ (q r : K) (_hq : q ≠ 0) (_hr : r ≠ 0),
    rationalBoost q * rationalBoost r = rationalBoost (q * r)) ∧
    (∀ (q r : K) (_hq : q ≠ 0) (_hr : r ≠ 0) (_hne : r ≠ 1),
    coarseLinkReport (q, q) = coarseLinkReport (q * r, q / r) ∧
      fineSeamLink (q, q) ≠ fineSeamLink (q * r, q / r)) ∧
    (∀ (q r : K) (_hq : q ≠ 0) (_hr : r ≠ 0),
    rationalBoost q * rationalBoost q = rationalBoost (q * r) * rationalBoost (q / r))

end Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement
