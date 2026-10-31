import ArtformScores.GravityBridge.BoundaryAdjointDefs

/-! # Source-bearing two-cell torsion contribution -/

namespace Artform.Scores.GravityBridge

noncomputable section

open Native

def twoCellTorsion (a m b j : ℚ) : ℚ :=
  nativeEdgeTorsion a m + nativeEdgeTorsion m b - j * m

def twoCellEffective (a b j : ℚ) : ℚ :=
  kappa / 2 * (b - a) ^ 2 - j * (a + b) / 2 - j ^ 2 / (8 * kappa)

def twoCellMiddle (a b j : ℚ) : ℚ := (a + b) / 2 + j / (4 * kappa)

end

end Artform.Scores.GravityBridge
