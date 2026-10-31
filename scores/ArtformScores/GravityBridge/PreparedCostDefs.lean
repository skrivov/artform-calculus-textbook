import ArtformScores.GravityBridge.Native.Preparation

/-! # Declared native block experiment and rational coefficient cost -/

namespace Artform.Scores.GravityBridge

noncomputable section

open Native

def connectionCoefficientCost (c : Fin 3 → ℚ) : ℚ := ∑ i, c i ^ 2

def oddConnectionMatch (z : ℚ) (c : Fin 3 → ℚ) : Prop := c 1 - c 2 = -4 * z / 103

end

end Artform.Scores.GravityBridge
