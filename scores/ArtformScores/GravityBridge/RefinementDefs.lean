import ArtformScores.GravityBridge.ChangingGeometryDefs

/-! # Retained edge detail and its explicit elimination data -/

namespace Artform.Scores.GravityBridge

noncomputable section

def refinedAction (h0 h1 c d j : ℚ) : ℚ :=
  (h0 / (h0 + h1) * c + d) ^ 2 / (2 * h0) +
    (h1 / (h0 + h1) * c - d) ^ 2 / (2 * h1) - j * d

def reducedAction (h0 h1 c j : ℚ) : ℚ :=
  c ^ 2 / (2 * (h0 + h1)) - h0 * h1 / (2 * (h0 + h1)) * j ^ 2

def stationaryDetail (h0 h1 j : ℚ) : ℚ := h0 * h1 / (h0 + h1) * j

def unequalFineStep (e : Fin 2 → ℚ) : Fin 2 → ℚ := ![2 * e 0, e 1 / 2]

def coarseDetailStep (x : ℚ × ℚ) : ℚ × ℚ := ((5 * x.1 + 3 * x.2) / 4, (3 * x.1 + 5 * x.2) / 4)

end

end Artform.Scores.GravityBridge
