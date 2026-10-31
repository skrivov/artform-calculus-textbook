import ArtformScores.GravityBridge.LinearDefs

/-! # A signed spatial symmetry class and an explicit periodic binary regulator -/

namespace Artform.Scores.GravityBridge

noncomputable section

def quadraticKinetic (a : Fin 4 → ℚ) (b : Fin 6 → ℚ) (k : Fin 4 → ℚ) : ℚ :=
  a 0 * (k 0) ^ 2 + a 1 * (k 1) ^ 2 + a 2 * (k 2) ^ 2 + a 3 * (k 3) ^ 2 +
  b 0 * k 0 * k 1 + b 1 * k 0 * k 2 + b 2 * k 0 * k 3 +
  b 3 * k 1 * k 2 + b 4 * k 1 * k 3 + b 5 * k 2 * k 3

def kineticReflection (i : Fin 4) (k : Fin 4 → ℚ) : Fin 4 → ℚ :=
  fun j => if j = i then -k j else k j

def kineticSwap12 (k : Fin 4 → ℚ) : Fin 4 → ℚ := ![k 0, k 2, k 1, k 3]
def kineticSwap23 (k : Fin 4 → ℚ) : Fin 4 → ℚ := ![k 0, k 1, k 3, k 2]

def spatialSignedKinetic (a : Fin 4 → ℚ) (b : Fin 6 → ℚ) : Prop :=
  (∀ i k, quadraticKinetic a b (kineticReflection i k) = quadraticKinetic a b k) ∧
  (∀ k, quadraticKinetic a b (kineticSwap12 k) = quadraticKinetic a b k) ∧
  (∀ k, quadraticKinetic a b (kineticSwap23 k) = quadraticKinetic a b k)

abbrev BinarySite := Fin 16

def binaryCharacter (k x : BinarySite) : ℚ :=
  ∏ i : Fin 4, if k.val.testBit i.val && x.val.testBit i.val then -1 else 1

def walshFour (x k : BinarySite) : ℚ := binaryCharacter k x / 4

def walshSourceGram (p k l : BinarySite) : ℚ :=
  ∑ x, walshFour x k * binaryCharacter p x * walshFour x l

def momentumAxis (i : Fin 4) : BinarySite := ⟨2 ^ i.val, by fin_cases i <;> decide⟩

def walshAxisDifference (i : Fin 4) (x k : BinarySite) : ℚ :=
  walshFour (x ^^^ momentumAxis i) k - walshFour x k

def modePrecision (ct cs : ℚ) (k : BinarySite) : ℚ :=
  1 + ct * (if k.val.testBit 0 then 1 else 0) +
    cs * ((if k.val.testBit 1 then 1 else 0) + (if k.val.testBit 2 then 1 else 0) +
      (if k.val.testBit 3 then 1 else 0))

def localPrecisionGram (ct cs : ℚ) (k l : BinarySite) : ℚ :=
  (∑ x, walshFour x k * walshFour x l) +
  ct / 4 * (∑ x, walshAxisDifference 0 x k * walshAxisDifference 0 x l) +
  cs / 4 * (∑ i : Fin 3, ∑ x,
    walshAxisDifference i.succ x k * walshAxisDifference i.succ x l)

def loopResponse (ct cs : ℚ) (i : Fin 4) : ℚ :=
  ∑ k : BinarySite, 1 / (modePrecision ct cs k * modePrecision ct cs (k ^^^ momentumAxis i))

abbrev AxisRepresentatives (i : Fin 4) := {k : BinarySite // k.val.testBit i.val = false}

def pairWeight (i : Fin 4) (k : AxisRepresentatives i) : ℚ :=
  modePrecision 2 1 k.val * modePrecision 2 1 (k.val ^^^ momentumAxis i)

end

end Artform.Scores.GravityBridge
