import ArtformScores.GravityBridge.Native.InverseJets.NormalPair

/-! # Complete normal divergence and the supplied physical third group -/

namespace Artform.Scores.GravityBridge.Native.NormalDivergence

open Matrix

variable {K : Type*} [Field K] [CharZero K]

abbrev V3 (K : Type*) := Fin 3 → K

abbrev M3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

def dot3 (x y : V3 K) : K := ∑ i, x i * y i

def antisymmetricFaces (c : V3 K) : M3 K := !![0, c 0, c 1;-c 0, 0, c 2;-c 1, -c 2, 0]

def normalVector (d : V3 K) (electric electricTime : M3 K) (faces : V3 K) : V3 K :=
  fun a => (-1 / 202 : K) * (
    (∑ i, d i * (electricTime i a - d i * electric i a))-
    (∑ b, d b * (electricTime a b - d a * electric a b))-
    ∑ j, (d a - d j) * d j * antisymmetricFaces faces a j)

def primaryDivergence (d faces : V3 K) : K := (1 / 101 : K) * (
  (d 0 - d 1) * d 0 * d 1 * faces 0 + (d 0 - d 2) * d 0 * d 2 * faces 1 +
    (d 1 - d 2) * d 1 * d 2 * faces 2)

def curlFaces (d u : V3 K) : V3 K :=
  ![d 0 * u 1 - d 1 * u 0, d 0 * u 2 - d 2 * u 0, d 1 * u 2 - d 2 * u 1]

def h1CutRow (p q ni0 nj0 ni1 nj1 ni2 nj2 : K) : K :=
  -((1 / 101 : K) * (101 / 97) * (101 / 103)) / 2 *
    ((p * nj2 - q * ni2) - (p + q) * (p * nj1 - q * ni1) + p * q * (p * nj0 - q * ni0))

noncomputable def referenceD : V3 ℂ := Complex.I • ![1, 2, 3]

noncomputable def physicalJ2 : V3 ℂ := (14 * (101 / 39964 : ℂ)) •
  ((1 / 35 : ℂ) • ![1, -68, 45])

noncomputable def physicalH1Faces : V3 ℂ :=
  (-((1 / 101 : ℂ) * (101 / 97) * (101 / 103))) • curlFaces referenceD physicalJ2

end Artform.Scores.GravityBridge.Native.NormalDivergence
