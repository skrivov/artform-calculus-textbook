import ArtformScores.GravityBridge.Native.NormalDivergence.PhysicalDefs

/-! # Complete normal divergence and the supplied physical third group -/

namespace Artform.Scores.GravityBridge.Native.NormalDivergence.Statement

open Matrix

/-- **GAC2:normal-divergence-physical-group**
(complete normal divergence and the supplied physical third group). -/
@[ledger "GAC2:normal-divergence-physical-group"]
def physicalLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (d : V3 K) (e et : M3 K) (c : V3 K),
    dot3 d (normalVector d e et c) = primaryDivergence d c) ∧
    (∀ (d u : V3 K),
    primaryDivergence d (curlFaces d u) = (1 / 101 : K) *
      ((∑ i, (d i) ^ 3) * dot3 d u - (∑ i, (d i) ^ 2) * dot3 (fun i => (d i) ^ 2) u)) ∧
    (∀ (p q s ji jj : K),
    h1CutRow p q 0 0 (s * p) (s * q) (2 * ji) (2 * jj) =
      -((1 / 101 : K) * (101 / 97) * (101 / 103)) * (p * jj - q * ji)) ∧
    (dot3 referenceD physicalJ2 = 0 ∧
    dot3 (fun i => (referenceD i) ^ 2) physicalJ2 = -268 * (101 / 39964 : ℂ) / 5) ∧
    (primaryDivergence referenceD physicalH1Faces =
      3752 * (1 / 101 : ℂ) ^ 2 * (101 / 97) * (101 / 103) * (101 / 39964) / 5)

end Artform.Scores.GravityBridge.Native.NormalDivergence.Statement
