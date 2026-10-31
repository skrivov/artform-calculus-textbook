import ArtformScores.GravityBridge.ClockDefs

/-! # Clock source response and coupling freedom -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:clock-coupling-response** (clock source response and coupling freedom). -/
@[ledger "GAC:clock-coupling-response"]
def clockLaw : Prop :=
  (∀ N a coupling prev current next source eps v : ℚ,
    twoEdgeClockAction N a coupling prev (current + eps * v) next source =
      twoEdgeClockAction N a coupling prev current next source +
      eps * (-coupling * a ^ 3 / N * (next - 2 * current + prev) - source) * v +
      eps ^ 2 * coupling * a ^ 3 / N * v ^ 2) ∧
  (∀ (N a coupling rate acceleration : ℚ) (n : ℤ),
    homogeneousClockForce N a coupling (quadraticClock rate acceleration) n =
      -2 * coupling * a ^ 3 / N * acceleration) ∧
  (∀ N a coupling rate : ℚ,
    quadraticClock rate 0 0 = 0 ∧ quadraticClock rate 0 1 = rate ∧
    ∀ n, homogeneousClockForce N a coupling (quadraticClock rate 0) n = 0) ∧
  (∀ N a coupling c : ℚ, c ≠ 0 →
    coupling * a ^ 3 / (c * N) = (coupling * a ^ 3 / N) / c) ∧
  (∀ coupling : ℝ,
    HasDerivAt (fun N : ℝ => coupling / (2 * N)) (-coupling / 2) 1)

end Artform.Scores.GravityBridge.Statement
