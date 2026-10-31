import ArtformScores.GravityBridge.RegulatorDefs

/-! # Spatial quadratic classification and exact lattice Fourier data -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:finite-regulator-symmetry** (spatial classification and exact lattice Fourier data). -/
@[ledger "GAC:finite-regulator-symmetry"]
def regulatorLaw : Prop :=
  (∀ (a : Fin 4 → ℚ) (b : Fin 6 → ℚ),
    spatialSignedKinetic a b ↔ b = 0 ∧ a 1 = a 2 ∧ a 2 = a 3) ∧
  (∀ ct cs : ℚ, spatialSignedKinetic ![ct, cs, cs, cs] 0) ∧
  (spatialSignedKinetic ![2, 1, 1, 1] 0 ∧
    quadraticKinetic ![2, 1, 1, 1] 0 ![1, 0, 0, 0] ≠
      quadraticKinetic ![2, 1, 1, 1] 0 ![0, 1, 0, 0]) ∧
  (∀ k l : BinarySite, (∑ x, walshFour x k * walshFour x l) = if k = l then 1 else 0) ∧
  (∀ (i : Fin 4) (k l : BinarySite),
    walshSourceGram (momentumAxis i) k l = if l = k ^^^ momentumAxis i then 1 else 0) ∧
  (∀ (i : Fin 4) (k l : BinarySite),
    (∑ x, walshAxisDifference i x k * walshAxisDifference i x l) =
      if k = l then 4 * (if k.val.testBit i.val then 1 else 0) else 0) ∧
  (∀ (ct cs : ℚ) (k l : BinarySite),
    localPrecisionGram ct cs k l = if k = l then modePrecision ct cs k else 0) ∧
  (∀ ct cs : ℚ, loopResponse ct cs 1 = loopResponse ct cs 2 ∧
    loopResponse ct cs 2 = loopResponse ct cs 3) ∧
  (loopResponse 2 1 0 = 19 / 10 ∧ loopResponse 2 1 1 = 34 / 15) ∧
  (∀ i : Fin 4, Fintype.card (AxisRepresentatives i) = 8) ∧
  (∀ (i : Fin 4) (k : BinarySite),
    ∃! r : AxisRepresentatives i, k = r.val ∨ k = r.val ^^^ momentumAxis i) ∧
  (∀ k : BinarySite, 1 ≤ modePrecision 2 1 k) ∧
  (∀ i : Fin 4, (∑ k : AxisRepresentatives i, 1 / pairWeight i k) = loopResponse 2 1 i / 2)

end Artform.Scores.GravityBridge.Statement
