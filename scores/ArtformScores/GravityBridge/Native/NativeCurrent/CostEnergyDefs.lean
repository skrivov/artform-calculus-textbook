import ArtformScores.GravityBridge.Native.TTCoordinates.Programs

/-! # Exact coefficient work does not fund quadratic energy -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent

open Matrix TTCoordinates



def originalLeadingEnergy (rho2 : ℚ) (q p : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  rho2 * (∑ i, ∑ j, (q i j) ^ 2) / 8 + (∑ i, ∑ j, (p i j) ^ 2) / 2

end Artform.Scores.GravityBridge.Native.NativeCurrent
