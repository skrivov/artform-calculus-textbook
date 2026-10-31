import ArtformScores.GravityBridge.Native.R2Defs

/-! # Original regular phase and its even determinant -/

namespace Artform.Scores.GravityBridge.Native.R2

open Complex

def evenDelta (q R a G : ℝ) : ℝ :=
  (1 + q ^ 2) * (1 + R) ^ 2 * (a ^ 2 + G) -
    (1 + q ^ 2 * (2 * a - 1) ^ 2 + 4 * q ^ 2 * G)

noncomputable def phaseNorm (q R a gamma s : ℝ) : ℝ :=
  4 * (a * s + (2 - 3 * a)) ^ 2 * Complex.normSq (phaseT q R a gamma) -
    R * s * (3 - s) * (phaseDelta q R a gamma) ^ 2

noncomputable def phaseP (q R a gamma : ℝ) : ℂ :=
  (1 + R : ℝ) * (1 - I * q) * (1 - zeta a gamma)
noncomputable def phaseQ (q a gamma : ℝ) : ℂ :=
  1 + I * q - 2 * I * q * star (zeta a gamma)

noncomputable def regularV (q R a gamma H : ℝ) : ℂ :=
  (-2 * H : ℝ) * phaseT q R a gamma / (phaseDelta q R a gamma : ℝ)

end Artform.Scores.GravityBridge.Native.R2
