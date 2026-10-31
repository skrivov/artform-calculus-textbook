import ArtformScores.GravityBridge.PreparedCostStatements

/-! # The partial connection matching class has an exact coefficient minimum -/

namespace Artform.Scores.GravityBridge

noncomputable section

open Native

lemma prepared_odd_match (z : ℚ) : oddConnectionMatch z (connectionPreparation z) := by
  norm_num [oddConnectionMatch, connectionPreparation]
  ring

lemma equation_implies_odd_match (z : ℚ) (c : Fin 3 → ℚ) (h : connectionEquation z c) :
    oddConnectionMatch z c := by
  rw [(connectionEquation_iff z c).mp h]
  exact prepared_odd_match z

lemma odd_connection_cost (z : ℚ) (c : Fin 3 → ℚ) (h : oddConnectionMatch z c) :
    connectionCoefficientCost c = 8 * z ^ 2 / 10609 + c 0 ^ 2 + (c 1 + c 2) ^ 2 / 2 := by
  change c 1 - c 2 = -4 * z / 103 at h
  have hp : c 1 = c 2 - 4 * z / 103 := by linarith
  norm_num [connectionCoefficientCost, Fin.sum_univ_succ]
  rw [hp]
  ring

lemma odd_cost_minimum (z : ℚ) (c : Fin 3 → ℚ) (h : oddConnectionMatch z c) :
    8 * z ^ 2 / 10609 ≤ connectionCoefficientCost c ∧
    (connectionCoefficientCost c = 8 * z ^ 2 / 10609 ↔ c = connectionPreparation z) := by
  rw [odd_connection_cost z c h]
  have hs0 := sq_nonneg (c 0)
  have hs12 := sq_nonneg (c 1 + c 2)
  constructor
  · linarith
  · constructor
    · intro he
      have hc0 : c 0 = 0 := by nlinarith
      have hc12 : c 1 + c 2 = 0 := by nlinarith
      change c 1 - c 2 = -4 * z / 103 at h
      ext i
      fin_cases i <;> norm_num [connectionPreparation] <;> linarith
    · intro he
      rw [he]
      norm_num [connectionPreparation]
      ring

lemma prepared_reset_experiment (z : ℚ) (hz : z ≠ 0) :
    ((z, connectionPreparation z) : ℚ × (Fin 3 → ℚ)).1 = (z, 0).1 ∧
    (connectionPreparation z 1 - connectionPreparation z 2) ≠ (0 : ℚ) ∧
    ¬ connectionEquation z 0 := by
  refine ⟨rfl, ?_, ?_⟩
  · have h := prepared_odd_match z
    change connectionPreparation z 1 - connectionPreparation z 2 = -4 * z / 103 at h
    rw [h]
    exact div_ne_zero (mul_ne_zero (by norm_num) hz) (by norm_num)
  · intro h
    have hm := equation_implies_odd_match z 0 h
    change 0 - 0 = -4 * z / 103 at hm
    have hzero : z = 0 := by linarith
    exact hz hzero

/-- **GAC:prepared-connection-cost** (declared coefficient cost, not physical energy). -/
@[ledger "GAC:prepared-connection-cost"]
theorem preparedCostLaw : Statement.preparedCostLaw := by
  exact ⟨prepared_odd_match, equation_implies_odd_match, odd_connection_cost,
    odd_cost_minimum, prepared_reset_experiment⟩

/-! ## Non-vacuity -/

example : oddConnectionMatch (23 / 10) (connectionPreparation (23 / 10)) ∧
    connectionCoefficientCost (connectionPreparation (23 / 10)) = 1058 / 265225 ∧
    (0 : ℚ) < 1058 / 265225 := by
  refine ⟨prepared_odd_match _, ?_, by norm_num⟩
  norm_num [connectionCoefficientCost, connectionPreparation, Fin.sum_univ_succ]

end

end Artform.Scores.GravityBridge
