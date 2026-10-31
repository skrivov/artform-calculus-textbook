import ArtformScores.GravityBridge.Native.Defs

/-! # Unique coupled selected-jet recurrences for the fixed reference -/

namespace Artform.Scores.GravityBridge.Native.SelectedJets

open Matrix



abbrev Vec3 := Fin 3 → ℚ

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℚ

def k : Vec3 := ![1, 2, 3]

def moment (n : ℕ) (y : Vec3) : ℚ := ∑ i, (k i) ^ n * y i

def hd : ℚ := 9999 / 9991

def dd : ℚ := 10201 / 10300

def ee : ℚ := 202 / 9991

def kap : ℚ := 1 / 101

def bb : ℚ := -10201 / 20600

def beta3 : ℚ := 1 / 19982

def cv : ℚ := beta3 - 2 * (-1 / 82400)

def outerK : Mat3 := fun i j => k i * k j

def principal : Mat3 := hd • 1 + ((dd - hd) / 14) • outerK

def principalInverse : Mat3 := hd⁻¹ • 1 + ((dd⁻¹ - hd⁻¹) / 14) • outerK

def selectedU : Vec3 := fun i =>
  (![31, 2582, -1419] i) / 103 + 2 * (![98, 2716, -1218] i) / 9991 -
    (![2059, 3314, 3765] i) / 20600

def w1 (y : Vec3) : ℚ := 18 * (hd + dd) * moment 1 y +
  7 * (dd - hd) * moment 2 y - 7056 * (kap * bb) / 5

def w2 (y : Vec3) : ℚ := 18 * (hd + dd) * moment 2 y +
  49 * (dd - hd) * moment 1 y + (1876 * hd - 18144 * (kap * bb)) / 5

structure SelectedJet where
  y : Vec3
  p1 : ℚ
  p2 : ℚ
  n1 : ℚ
  n2 : ℚ
  deriving DecidableEq

def selectedJet : SelectedJet where
  y := (101 / 490 : ℚ) • (principalInverse *ᵥ selectedU)
  p1 := -w1 ((101 / 490 : ℚ) • (principalInverse *ᵥ selectedU)) / (7 * dd)
  p2 := -(hd⁻¹ * w2 ((101 / 490 : ℚ) • (principalInverse *ᵥ selectedU)) +
    (dd⁻¹ - hd⁻¹) * (18 / 7) * w1 ((101 / 490 : ℚ) • (principalInverse *ᵥ selectedU))) / 7
  n1 := -297 / 505 - (10300 * cv / 707) * (14 * moment 2 ((101 / 490 : ℚ) •
    (principalInverse *ᵥ selectedU)) - 36 * moment 1 ((101 / 490 : ℚ) •
    (principalInverse *ᵥ selectedU)))
  n2 := (202 * hd⁻¹ * ((38 * cv / 7) * moment 1 ((101 / 490 : ℚ) •
    (principalInverse *ᵥ selectedU)) - 5332 * beta3 / 5) + 36 * (-297 / 505 - (10300 * cv / 707) *
    (14 * moment 2 ((101 / 490 : ℚ) • (principalInverse *ᵥ selectedU))-
      36 * moment 1 ((101 / 490 : ℚ) • (principalInverse *ᵥ selectedU))))) / 14

def jetEquations (s : SelectedJet) : Prop :=
  principal *ᵥ s.y = (101 / 490 : ℚ) • selectedU ∧
  7 * dd * s.p1 = -w1 s.y ∧
  7 * s.p2 = -(hd⁻¹ * w2 s.y + (dd⁻¹ - hd⁻¹) * (18 / 7) * w1 s.y) ∧
  s.n1 = -297 / 505 - (10300 * cv / 707) * (14 * moment 2 s.y - 36 * moment 1 s.y) ∧
  14 * s.n2 = 202 * hd⁻¹ * ((38 * cv / 7) * moment 1 s.y - 5332 * beta3 / 5) + 36 * s.n1

end Artform.Scores.GravityBridge.Native.SelectedJets
