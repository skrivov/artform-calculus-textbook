import ArtformScores.GravityBridge.Native.SelectedJets.Recurrences
import Mathlib.Data.ZMod.Basic

/-! # Exact value and regular-prime replay of the supplied four-group recipe -/

namespace Artform.Scores.GravityBridge.Native.LongitudinalRecipe

open Matrix

variable {K : Type*} [Field K]

abbrev Vec3 (K : Type*) := Fin 3 → K

abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

def k : Vec3 K := ![1, 2, 3]

def moment (n : ℕ) (v : Vec3 K) : K := ∑ i, (k i) ^ n * v i

def kap : K := 1 / 101

def aa : K := 101 / 103

def gg : K := 101 / 97

def ee : K := 202 / 9991

def hd : K := 9999 / 9991

def dd : K := 10201 / 10300

def betaPhysical : K := 101 / 39964

def betaThird : K := 1 / 19982

def bb : K := -10201 / 20600

def cv : K := betaThird - 2 * (-1 / 82400)

def outerK : Mat3 K := fun i j => k i * k j

def inversePrincipal : Mat3 K := (hd : K)⁻¹ • (1 : Mat3 K) + (((dd : K)⁻¹ - (hd : K)⁻¹) / 14) •
  outerK

def forcingU : Vec3 K := fun i => (![31, 2582, -1419] i) / 103 +
  2 * (![98, 2716, -1218] i) / 9991 - (![2059, 3314, 3765] i) / 20600

def selectedY : Vec3 K := (101 / 490 : K) • (inversePrincipal *ᵥ forcingU)

def m1 : K := moment 1 selectedY

def m2 : K := moment 2 selectedY

def m3 : K := moment 3 selectedY

def w1 : K := 18 * (hd + dd) * m1 + 7 * (dd - hd) * m2 - 7056 * (kap * bb) / 5

def w2 : K := 18 * (hd + dd) * m2 + 49 * (dd - hd) * m1 + (1876 * hd - 18144 * (kap * bb)) / 5

def p1 : K := -w1 / (7 * dd)

def p2 : K := -(hd⁻¹ * w2 + (dd⁻¹ - hd⁻¹) * (18 / 7) * w1) / 7

def n1 : K := -297 / 505 - (10300 * cv / 707) * (14 * m2 - 36 * m1)

def n2 : K := (202 * hd⁻¹ * ((38 * cv / 7) * m1 - 5332 * betaThird / 5) + 36 * n1) / 14

def bMoment : K := 14 * p2 - 36 * p1

def cMoment : K := -36 * m2 + 98 * m1

def dMoment : K := -14 * m3 + 98 * m1

def rz : K := 14 * n2 - 36 * n1

def hMoment : K := bMoment - dMoment

def a5 : K := kap * aa ^ 2 / 12

def c4 : K := kap ^ 2 * aa ^ 2 * gg ^ 2 / 2

def bc4 : K := (1 - 4 * kap) * c4

def b4 : K := -a5 + bc4

def l5 : K := a5 + ee / 24

def l4e : K := b4 + ee / 24

def l4s : K := c4 - ee / 24

def fullThirdSourceDerivative : K := kap ^ 2 * gg * aa * hMoment / 2 - kap * ee * rz / 2

def group2 : K := -fullThirdSourceDerivative / 6 + 1092 * betaThird / 5 - 36 * kap * (hd + ee) *
  betaThird

def group3 : K := 3752 * kap ^ 2 * gg * aa * betaPhysical / 5

def group4 : K := kap ^ 2 * aa ^ 2 * rz / 12

def group5 : K := kap * ((341 * a5 + 2935 * bc4) / 5 + 6211 * ee / 120)-
  kap * (l5 * bMoment + l4e * cMoment + l4s * dMoment) / 2

def allGroups : Fin 4 → K := ![group2, group3, group4, group5]

def total : K := ∑ i, allGroups i

def recipeJet : SelectedJets.SelectedJet where
  y := selectedY
  p1 := p1
  p2 := p2
  n1 := n1
  n2 := n2

def denominatorSites : List ℕ :=
  [2, 3, 5, 6, 7, 11, 12, 14, 24, 97, 101, 103, 120, 490, 505, 707, 9991, 9999, 10201,
    10300, 19982, 20600, 39964, 82400]

end Artform.Scores.GravityBridge.Native.LongitudinalRecipe
