import ArtformScores.GravityBridge.Native.R2Defs

/-! # Native R2 constant remainders with their shared factor retained -/

namespace Artform.Scores.GravityBridge.Native.R2

open Polynomial

noncomputable def constantSeeds (R a : ℝ) : Fin 4 → ℝ :=
  let t := (103 / 2 : ℝ)
  let c := 1 + t
  let u := 1 + R
  let m := 1 + (2 + 3 * t) * R + c * R ^ 2
  let v := 1 + c * R
  let p := m * a - v
  let j0 := 1 - u * a
  ![p + t * (4 * a - 1) * j0,
    (4 * a - 1) * p - j0,
    u + (4 * a - 1) * m,
    t * u * (4 * a - 1) - m]

noncomputable def constantQuotient (R a G : ℝ) (i : Fin 4) : ℝ :=
  -6 * R * constantSeeds R a i - 2 * (rowPolys R a G i).coeff 2 +
    2 * (5 - 8 * a + 6 * G) * (rowPolys R a G i).coeff 3

end Artform.Scores.GravityBridge.Native.R2
