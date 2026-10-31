import ArtformScores.GravityBridge.Native.DistinctBlock

/-! # The original signed block through a quadratic matrix relation -/

namespace Artform.Scores.GravityBridge.Native.Retrospective

open Matrix



def paramConnection (t : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  curvatureBlock + (2 * t) • (torsionBlock.transpose * facePairing * torsionBlock)

def inverseDenominator (t : ℚ) : ℚ := 2 * (1 - 4 * t) * (1 + 2 * t)

def inverseNumerator (t : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (6 * t - 1) • 1 + (1 - 2 * t) • curvatureBlock

def polynomialInverse (t : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (inverseDenominator t)⁻¹ • inverseNumerator t

end Artform.Scores.GravityBridge.Native.Retrospective
