import ArtformScores.GravityBridge.ClockStatements

/-! # A normalized affine clock leaves the matter coefficient free -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma two_edge_clock_variation (N a coupling prev current next source eps v : ℚ) :
    twoEdgeClockAction N a coupling prev (current + eps * v) next source =
      twoEdgeClockAction N a coupling prev current next source +
      eps * (-coupling * a ^ 3 / N * (next - 2 * current + prev) - source) * v +
      eps ^ 2 * coupling * a ^ 3 / N * v ^ 2 := by
  dsimp [twoEdgeClockAction]
  ring

lemma clock_response (N a coupling rate acceleration : ℚ) (n : ℤ) :
    homogeneousClockForce N a coupling (quadraticClock rate acceleration) n =
      -2 * coupling * a ^ 3 / N * acceleration := by
  simp [homogeneousClockForce, clockSecondDifference, quadraticClock]
  ring

lemma affine_clock_no_selection (N a coupling rate : ℚ) :
    quadraticClock rate 0 0 = 0 ∧ quadraticClock rate 0 1 = rate ∧
    ∀ n, homogeneousClockForce N a coupling (quadraticClock rate 0) n = 0 := by
  refine ⟨by simp [quadraticClock], by simp [quadraticClock], ?_⟩
  intro n
  rw [clock_response]
  ring

lemma clock_time_weight_rescaling (N a coupling c : ℚ) (hc : c ≠ 0) :
    coupling * a ^ 3 / (c * N) = (coupling * a ^ 3 / N) / c := by
  field_simp

lemma lapse_density_derivative (coupling : ℝ) :
    HasDerivAt (fun N : ℝ => coupling / (2 * N)) (-coupling / 2) 1 := by
  have h : HasDerivAt (fun N : ℝ => coupling / (2 * N))
      ((0 * (2 * 1) - (coupling) * (0 * 1 + 2 * 1)) / (2 * 1) ^ 2) 1 :=
    (hasDerivAt_const (1 : ℝ) (coupling)).div
      ((hasDerivAt_const (1 : ℝ) (2 : ℝ)).mul (hasDerivAt_id 1)) (by norm_num)
  convert h using 1
  ring

/-- **GAC:clock-coupling-response** (clock equations do not by themselves select a coupling). -/
@[ledger "GAC:clock-coupling-response"]
theorem clockLaw : Statement.clockLaw := by
  exact ⟨two_edge_clock_variation, clock_response, affine_clock_no_selection,
    clock_time_weight_rescaling, lapse_density_derivative⟩

/-! ## Non-vacuity -/

example : (∀ n, homogeneousClockForce 1 1 1 (quadraticClock 1 0) n = 0) ∧
    (∀ n, homogeneousClockForce 1 1 7 (quadraticClock 1 0) n = 0) ∧
    homogeneousClockForce 1 1 7 (quadraticClock 0 1) 0 = -14 := by
  refine ⟨(affine_clock_no_selection 1 1 1 1).2.2,
    (affine_clock_no_selection 1 1 7 1).2.2, ?_⟩
  norm_num [homogeneousClockForce, clockSecondDifference, quadraticClock]

end

end Artform.Scores.GravityBridge
