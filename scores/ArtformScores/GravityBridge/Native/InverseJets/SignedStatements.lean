import ArtformScores.GravityBridge.Native.InverseJets.SignedDefs
/-! # Original signed physical block and ordered inverse contacts -/
namespace Artform.Scores.GravityBridge.Native.InverseJets.Statement
open Matrix
open Full40
open Retrospective
/-- **GAC2:signed-ordered-inverse-contacts**
(original signed physical block and ordered inverse contacts). -/
@[ledger "GAC2:signed-ordered-inverse-contacts"]
def signedLaw : Prop :=
    (∀ (z : Fin 3 → ℚ),
    physicalTorsionRows z = signedC *ᵥ z) ∧
    (∀ (z : Fin 3 → ℚ),
    -physicalConnection z = distinctInput 0 ![-z 0, z 1, -z 2]) ∧
    (signedN0 * signedH0 = 1 ∧ signedH0 * signedN0 = 1 ∧
    signedBc * signedBcInverse = 1 ∧ signedC *ᵥ signedV = (-2 : ℚ) • signedW) ∧
    (∀ (l p q : ℚ),
    firstN l p q = (1/101 : ℚ) • !![0, q-p, q-l;p-q, 0, l-p;l-q, p-l, 0]) ∧
    (∀ (l p q : ℚ),
    firstH l p q = (1/101 * signedG * signedA : ℚ) •
      !![0, p-q, l-q;q-p, 0, p-l;q-l, l-p, 0]) ∧
    (∀ (l p q : ℚ),
    secondN l p q = sourceN2 l p q) ∧
    (∀ (l p q : ℚ),
    signedN0 * firstH l p q + firstN l p q * signedH0 = 0) ∧
    (∀ (l p q : ℚ),
    signedN0 * secondH l p q + firstN l p q * firstH l p q +
      secondN l p q * signedH0 = 0) ∧
    (∀ (x y : ℚ),
    (secondH 1 0 0 *ᵥ ![x, y, 0]) 2 =
      ((1/101 : ℚ)^2 * signedA^2 * signedG) * (x-y)) ∧
    (((secondH 1 1 0 - secondH 1 0 0 - secondH 0 1 0) *ᵥ ![1, 1, 0]) 2 =
      (1/101 : ℚ)^2 * signedA^2 * signedG ∧
    ((secondH 1 0 1 - secondH 1 0 0 - secondH 0 0 1) *ᵥ ![1, 1, 0]) 2 =
      -(1/101 : ℚ)^2 * signedA^2 * signedG)
end Artform.Scores.GravityBridge.Native.InverseJets.Statement
