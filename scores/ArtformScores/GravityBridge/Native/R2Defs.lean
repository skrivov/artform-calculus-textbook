import ArtformScores.GravityBridge.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Degree.Support

/-! # The literal four native R2 rows

The generic expression permits evaluation as either a real polynomial or its
value at a latitude. `half` is supplied explicitly so the same expression can
be used in a polynomial ring, without division by a polynomial.
-/

namespace Artform.Scores.GravityBridge.Native.R2

open Polynomial Complex

/-- M178's four cubic products, in the order Pe,Qe,Po,Qo. -/
def rowExpr {K : Type*} [CommRing K] (t half R a G s : K) : Fin 4 → K :=
  let c := 1 + t
  let u := 1 + R
  let b := 2 - 3 * a
  let h := a * s + b
  let D := 3 - s
  let d := c * u ^ 2 * (a ^ 2 + G) - (1 + t * (2 * a - 1) ^ 2 + 4 * t * G)
  let m := 1 + (2 + 3 * t) * R + c * R ^ 2
  let v := 1 + c * R
  let p := m * a - v
  let j0 := 1 - u * a
  let w := 3 * half + a - 3 * a ^ 2 + s * (a - half - G)
  let j := 1 + s
  let Ub := 2 * s + b
  let Vb := b * (4 * a - 1) + s * (4 * a - 2 - 4 * G)
  let f := 2 * u * w + Ub - 3 * a
  let g := Vb - a - 2 * R * w
  let alpha := 2 * R * j - 3 * s - 1
  let beta := 2 * u * j + s + 3
  let Ce := w * p - j * m * G
  let De := w * j0 + j * u * G
  let Eo := w * u - j * j0
  let Fo := w * m + j * p
  let Ie := Ub * p + t * Vb * j0 + G * s * (m - 3 * t * u)
  let Je := Vb * p - Ub * j0 + G * s * (3 * m + u)
  let Ko := Ub * u + Vb * m + s * (j0 - 3 * p)
  let Lo := t * u * Vb - m * Ub + s * (p + 3 * t * j0)
  ![s * D * R * (d * f + 4 * t * G * alpha) -
      4 * h * s * (u * Ce + t * R * De) - 2 * R * h * D * Ie,
    s * D * R * (d * g + 4 * G * beta) -
      4 * h * s * (u * De - R * Ce) - 2 * R * h * D * Je,
    s * D * R * (d * alpha + 4 * f) -
      4 * h * s * (u * Eo + R * Fo) - 2 * R * h * D * Ko,
    s * D * R * (d * beta + 4 * t * g) -
      4 * h * s * (u * Fo - t * R * Eo) - 2 * R * h * D * Lo]

/-- Physical t and exact rational half; no chart coefficient is inverted. -/
noncomputable def rows (R a G s : ℝ) : Fin 4 → ℝ :=
  rowExpr (103 / 2) (1 / 2) R a G s

/-- The four polynomials at fixed R,a,G, with latitude the indeterminate. -/
noncomputable def rowPolys (R a G : ℝ) : Fin 4 → Polynomial ℝ :=
  rowExpr (C (103 / 2)) (C (1 / 2)) (C R) (C a) (C G) X

/-- The original monic normal equation in a=1-x coordinates. -/
def normal {K : Type*} [CommRing K] (a G s : K) : K :=
  s ^ 2 + (5 - 8 * a + 6 * G) * s + 2 * (2 - 3 * a) ^ 2

/-- Original complex normal value zeta. -/
noncomputable def zeta (a gamma : ℝ) : ℂ := (1 - a : ℝ) + I * gamma

/-- The original W, before using the normal equation. -/
noncomputable def originalW (a gamma s : ℝ) : ℂ :=
  let h := a * s + (2 - 3 * a)
  (h ^ 2 + s * (3 - s) * ((1 - a) ^ 2 + gamma ^ 2) : ℝ) +
    (s * (1 + s) : ℝ) * zeta a gamma

/-- Original Bhat=E(s Bc+2iqh)+(h+2s zeta)Q with Q's original sign. -/
noncomputable def originalBhat (q a gamma s : ℝ) : ℂ :=
  let h := a * s + (2 - 3 * a)
  let z := zeta a gamma
  let E := 1 - z
  let Bc := 1 - I * q
  let Q := 1 + I * q - 2 * I * q * star z
  E * ((s : ℂ) * Bc + 2 * I * q * h) + ((h : ℂ) + 2 * s * z) * Q

/-- The original complex L. -/
noncomputable def phaseL (q R : ℝ) : ℂ := (1 + R : ℝ) - I * q * R

/-- The original regular-phase numerator. -/
noncomputable def phaseT (q R a gamma : ℝ) : ℂ :=
  let t := q ^ 2
  let c := 1 + t
  let u := 1 + R
  let m := 1 + (2 + 3 * t) * R + c * R ^ 2
  let v := 1 + c * R
  let p := m * a - v
  let j0 := 1 - u * a
  (p : ℂ) + I * q * j0 + gamma * (q * u + I * m)

/-- The original regular-phase real determinant, including its gamma sign. -/
noncomputable def phaseDelta (q R a gamma : ℝ) : ℝ :=
  (1 + q ^ 2) * (1 + R) ^ 2 * (a ^ 2 + gamma ^ 2) -
    (1 + q ^ 2 * (2 * a - 1) ^ 2 + 4 * q ^ 2 * gamma ^ 2) + 4 * q * gamma

/-- Corrected original J (5edba section 4), with literal Delta and T. -/
noncomputable def originalJ (q R a gamma s : ℝ) : ℂ :=
  let h := a * s + (2 - 3 * a)
  let D := 3 - s
  let T := phaseT q R a gamma
  let Delta := phaseDelta q R a gamma
  let E := 1 - zeta a gamma
  let Ahat := 2 * phaseL q R * originalW a gamma s
  let Bhat := originalBhat q a gamma s
  (R * D * Delta : ℝ) * Ahat + (R * s * D * Delta : ℝ) * (Bhat - E * (3 + I * q)) -
    2 * h * Ahat * T - 2 * R * h * D * Bhat * star T

/-- The unmultiplied affine trace of 5edba section 4, with every denominator. -/
noncomputable def traceResidual (q R a gamma s : ℝ) : ℂ :=
  let h := a * s + (2 - 3 * a)
  let D := 3 - s
  let E := 1 - zeta a gamma
  let Delta : ℂ := phaseDelta q R a gamma
  let T := phaseT q R a gamma
  let Atr := 2 * phaseL q R * originalW a gamma s / ((s * D : ℝ) * E)
  let Btr := originalBhat q a gamma s / E
  (R * D : ℝ) * Atr + R * Btr - R * (3 + I * q) -
    2 * h * Atr * T / Delta - 2 * R * h * Btr * star T / ((s : ℂ) * Delta)

/-- The affine coefficient of any cubic after division by the monic normal. -/
noncomputable def ell (a G : ℝ) (P : Polynomial ℝ) : ℝ :=
  let nu := 5 - 8 * a + 6 * G
  P.coeff 1 - nu * P.coeff 2 + (nu ^ 2 - 2 * (2 - 3 * a) ^ 2) * P.coeff 3

/-- The constant remainder, including its entire possible zero stratum. -/
noncomputable def remainderConst (a G : ℝ) (P : Polynomial ℝ) : ℝ :=
  let nu := 5 - 8 * a + 6 * G
  let k := 2 * (2 - 3 * a) ^ 2
  P.coeff 0 - k * P.coeff 2 + nu * k * P.coeff 3

end Artform.Scores.GravityBridge.Native.R2
