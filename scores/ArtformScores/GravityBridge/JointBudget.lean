import ArtformScores.GravityBridge.JointBudgetStatements
/-! # Joint angular spacing and nonlinear budget audit -/
namespace Artform.Scores.GravityBridge
noncomputable section
open Native.R8
lemma shrinking_angle_remainder (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    (2 ≤ radialSq (approachingRay h) ∧ radialSq (approachingRay h) ≤ 5) ∧
    leadingScalar (approachingRay h) ≠ 0 ∧
    |cancellingAnnularRemainder h| ≤ (metricCoefficient : ℝ) * h ^ 5 ∧
    h ^ 4 * leadingScalar (approachingRay h) + cancellingAnnularRemainder h = 0 := by
  have hf := near_ray_bounds h hh h1
  have hn := (near_ray_inverse h hh h1).1
  have hc : 0 < (metricCoefficient : ℝ) := by have he := metricCoefficient_lower; linarith
  refine ⟨hf.1, hn, ?_, ?_⟩
  · rw [cancellingAnnularRemainder, abs_mul, abs_neg,
      abs_of_nonneg (pow_nonneg hh.le 4), leadingScalar, abs_mul, abs_neg,
      abs_of_pos hc, abs_of_pos hf.2.1]
    calc
      h ^ 4 * ((metricCoefficient : ℝ) * angularDefect (approachingRay h)) ≤
          h ^ 4 * ((metricCoefficient : ℝ) * h ^ 2) := by gcongr; exact hf.2.2
      _ = ((metricCoefficient : ℝ) * h ^ 5) * h := by ring
      _ ≤ ((metricCoefficient : ℝ) * h ^ 5) * 1 := by gcongr
      _ = (metricCoefficient : ℝ) * h ^ 5 := by ring
  · dsimp [cancellingAnnularRemainder]
    ring
lemma nonlinear_amplitude_budget (h d amplitude C : ℝ) (hh : 0 < h) (hd : 0 < d)
    (ha : 0 < amplitude) :
    amplitude ^ 2 / (h ^ 4 * d) ≤ C * amplitude ↔ amplitude ≤ C * h ^ 4 * d := by
  rw [div_le_iff₀ (by positivity : 0 < h ^ 4 * d)]
  constructor
  · intro he
    nlinarith
  · intro he
    nlinarith
/-- **GAC:joint-remainder-budget** (joint angular spacing and nonlinear budget audit). -/
@[ledger "GAC:joint-remainder-budget"]
theorem jointBudgetLaw : Statement.jointBudgetLaw := by
  exact ⟨shrinking_angle_remainder, nonlinear_amplitude_budget⟩
/-! ## Non-vacuity -/
example : leadingScalar (approachingRay (1 / 100)) ≠ 0 ∧
    |cancellingAnnularRemainder (1 / 100)| ≤ (metricCoefficient : ℝ) * (1 / 100) ^ 5 ∧
    (1 / 100 : ℝ) ^ 4 * leadingScalar (approachingRay (1 / 100)) +
      cancellingAnnularRemainder (1 / 100) = 0 :=
  (shrinking_angle_remainder (1 / 100) (by norm_num) (by norm_num)).2
end
end Artform.Scores.GravityBridge
