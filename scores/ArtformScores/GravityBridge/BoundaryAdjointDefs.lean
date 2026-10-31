import ArtformScores.GravityBridge.Native.PreparationDefs

/-! # Finite shift boundary data and a source-pinned torsion component -/

namespace Artform.Scores.GravityBridge

noncomputable section

def forwardDifference (f : ℕ → ℚ) (i : ℕ) : ℚ := f (i + 1) - f i

def edgeBoundaryPair (f g : ℕ → ℚ) (n : ℕ) : ℚ := f n * g n - f 0 * g 0

def nativeEdgeTorsion (u0 u1 : ℚ) : ℚ := Native.kappa * (u1 - u0) ^ 2

end

end Artform.Scores.GravityBridge
