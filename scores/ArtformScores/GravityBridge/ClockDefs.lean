import ArtformScores.GravityBridge.MatterDefs

/-! # Temporal clock forces and the independent coupling parameter -/

namespace Artform.Scores.GravityBridge

noncomputable section

def clockSecondDifference (phi : ℤ → ℚ) (n : ℤ) : ℚ :=
  phi (n + 1) - 2 * phi n + phi (n - 1)

def homogeneousClockForce (N a coupling : ℚ) (phi : ℤ → ℚ) (n : ℤ) : ℚ :=
  -coupling * a ^ 3 / N * clockSecondDifference phi n

def quadraticClock (rate acceleration : ℚ) (n : ℤ) : ℚ :=
  rate * n + acceleration * n ^ 2

def twoEdgeClockAction (N a coupling prev current next source : ℚ) : ℚ :=
  coupling * a ^ 3 / (2 * N) * ((current - prev) ^ 2 + (next - current) ^ 2) -
    source * current

end

end Artform.Scores.GravityBridge
