import ArtformScores.GravityBridge.Native.Defs

/-! # Literal leading metric-cut scalar and exceptional-ray distance -/

namespace Artform.Scores.GravityBridge.Native.R8

open Finset

noncomputable def radialSq (k : Fin 3 → ℝ) : ℝ := ∑ i, (k i) ^ 2
noncomputable def angularDefect (k : Fin 3 → ℝ) : ℝ :=
  (∑ i, (k i) ^ 4) - (∑ i, (k i) ^ 3) ^ 2 / radialSq k
noncomputable def pairNumerator (k : Fin 3 → ℝ) : ℝ :=
  (k 0 * k 1 * (k 0 - k 1)) ^ 2 +
    (k 0 * k 2 * (k 0 - k 2)) ^ 2 + (k 1 * k 2 * (k 1 - k 2)) ^ 2

def rayPoint (m : ℝ) (b : Fin 3 → Bool) (i : Fin 3) : ℝ := if b i then m else 0
noncomputable def rayError (k : Fin 3 → ℝ) (m : ℝ) (b : Fin 3 → Bool) : ℝ :=
  ∑ i, (k i - rayPoint m b i) ^ 2

def RaySeparated (k : Fin 3 → ℝ) (delta : ℝ) : Prop :=
  ∀ m b, (∃ i, b i = true) → delta ^ 2 ≤ rayError k m b

noncomputable def projectedSquare (k : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (k i) ^ 2 - k i * (∑ j, (k j) ^ 3) / radialSq k

def metricCoefficient : ℚ :=
  let kappa := (1 / 101 : ℚ)
  let A := (101 / 103 : ℚ)
  let g := (101 / 97 : ℚ)
  let E := (202 / 9991 : ℚ)
  let Hd := (9999 / 9991 : ℚ)
  let D := (10201 / 10300 : ℚ)
  let beta := (-2422 / (3 * 9991) : ℚ)
  kappa * (Hd + (kappa * A ^ 2 + E) * (Hd - D) / Hd) / 12 +
    kappa ^ 4 * g ^ 2 * A ^ 2 / (4 * beta)

noncomputable def leadingScalar (k : Fin 3 → ℝ) : ℝ := -(metricCoefficient : ℝ) * angularDefect k

noncomputable def approachingRay (e : ℝ) : Fin 3 → ℝ := ![1, 1 + e, 0]

end Artform.Scores.GravityBridge.Native.R8
