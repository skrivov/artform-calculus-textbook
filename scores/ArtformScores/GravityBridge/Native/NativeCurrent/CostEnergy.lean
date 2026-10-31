import ArtformScores.GravityBridge.Native.NativeCurrent.CostEnergyStatements

/-! # Exact coefficient work does not fund quadratic energy -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent

open Matrix TTCoordinates



open Matrix TTCoordinates

lemma original_reference_energy (a : ℚ) :
    originalLeadingEnergy 14 (a • polarization) 0 = 7 * a ^ 2 / 2 := by
  norm_num [originalLeadingEnergy, polarization, Fin.sum_univ_succ]
  ring

lemma same_program_all_amplitudes (a : ℚ) :
    ttScales contractedForcingProgram = 1 ∧ ttAdds contractedForcingProgram = 0 ∧
    evalTTExpr (a • polarization) contractedForcingProgram = (36 / 505 : ℚ) * a := by
  refine ⟨rfl, rfl, ?_⟩
  norm_num [evalTTExpr, contractedForcingProgram, polarization]
  ring

lemma same_cost_unbounded_quadratic_energy (M : ℚ) :
    ∃ a : ℚ, ttScales contractedForcingProgram = 1 ∧
      M < originalLeadingEnergy 14 (a • polarization) 0 := by
  refine ⟨M ^ 2 + 1, rfl, ?_⟩
  rw [original_reference_energy]
  have h1 : M < M ^ 2 + 1 := by nlinarith [sq_nonneg (M - 1 / 2)]
  have h2 : 1 ≤ M ^ 2 + 1 := by nlinarith [sq_nonneg M]
  have h3 : M ^ 2 + 1 ≤ (M ^ 2 + 1) ^ 2 := by nlinarith
  nlinarith

/-- **GAC2:declared-cost-quadratic-energy**
(exact coefficient work does not fund quadratic energy). -/
@[ledger "GAC2:declared-cost-quadratic-energy"]
theorem costEnergyLaw : Statement.costEnergyLaw := by
  exact ⟨original_reference_energy,
    same_program_all_amplitudes,
    same_cost_unbounded_quadratic_energy⟩

/-! ## Non-vacuity -/

example : originalLeadingEnergy 14 polarization 0 = 7 / 2 ∧
    originalLeadingEnergy 14 ((2 : ℚ) • polarization) 0 = 14 := by
  constructor
  · norm_num [originalLeadingEnergy, polarization, Fin.sum_univ_succ]
  · norm_num [original_reference_energy]

end Artform.Scores.GravityBridge.Native.NativeCurrent
