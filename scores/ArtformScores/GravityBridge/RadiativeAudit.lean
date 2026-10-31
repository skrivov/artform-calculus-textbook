import ArtformScores.GravityBridge.RadiativeAuditStatements
/-! # Finite amplitude response and parameter freedom -/
namespace Artform.Scores.GravityBridge
noncomputable section
lemma finite_loop_gap_positive (s : ℝ) (hs : s ^ 2 ≤ 1 / 10000) (hn : s ≠ 0) :
    (9 / 100 : ℝ) * s ^ 2 ≤ regulatorFreeEnergy 0 s - regulatorFreeEnergy 1 s ∧
      0 < regulatorFreeEnergy 0 s - regulatorFreeEnergy 1 s := by
  have hw : s ^ 2 ≤ (1 / 2 : ℝ) := by linarith
  have h0 := abs_le.mp (regulator_loop_error 0 s hw)
  have h1 := abs_le.mp (regulator_loop_error 1 s hw)
  rw [regulator_loop_gap.1] at h0
  rw [regulator_loop_gap.2.1] at h1
  have hb : s ^ 4 ≤ s ^ 2 / 10000 := by
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg s)]
  have hpos : 0 < s ^ 2 := sq_pos_of_ne_zero hn
  constructor <;> nlinarith
lemma finite_loop_matching (bt bs g : ℝ) :
    bt + g ^ 2 * regulatorLoopCoefficient 0 = bs + g ^ 2 * regulatorLoopCoefficient 1 ↔
      bt - bs = -(11 / 120 : ℝ) * g ^ 2 := by
  rw [regulator_loop_gap.1, regulator_loop_gap.2.1]
  constructor <;> intro h <;> nlinarith
lemma equal_bare_loop_split (b g : ℝ) (hg : g ≠ 0) :
    b + g ^ 2 * regulatorLoopCoefficient 0 ≠ b + g ^ 2 * regulatorLoopCoefficient 1 := by
  intro h
  have hm := (finite_loop_matching b b g).mp h
  nlinarith [sq_pos_of_ne_zero hg]
/-- **GAC:finite-response-audit** (finite amplitude response and parameter freedom). -/
@[ledger "GAC:finite-response-audit"]
theorem radiativeAuditLaw : Statement.radiativeAuditLaw := by
  exact ⟨finite_loop_gap_positive, finite_loop_matching, equal_bare_loop_split⟩
/-! ## Non-vacuity -/
example : (9 / 1000000 : ℝ) ≤ regulatorFreeEnergy 0 (1 / 100) -
      regulatorFreeEnergy 1 (1 / 100) := by
  convert (finite_loop_gap_positive (1 / 100) (by norm_num) (by norm_num)).1 using 1
  norm_num
example : (0 : ℝ) + regulatorLoopCoefficient 0 = 11 / 120 + regulatorLoopCoefficient 1 := by
  rw [regulator_loop_gap.1, regulator_loop_gap.2.1]
  norm_num
end
end Artform.Scores.GravityBridge
