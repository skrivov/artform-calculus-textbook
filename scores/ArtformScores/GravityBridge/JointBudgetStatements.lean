import ArtformScores.GravityBridge.JointBudgetDefs
/-! # Joint angular spacing and nonlinear budget audit -/
namespace Artform.Scores.GravityBridge.Statement
open Native.R8
/-- **GAC:joint-remainder-budget** (joint angular spacing and nonlinear budget audit). -/
@[ledger "GAC:joint-remainder-budget"]
def jointBudgetLaw : Prop :=
  (∀ (h : ℝ) (_hh : 0 < h) (_h1 : h ≤ 1),
    (2 ≤ radialSq (approachingRay h) ∧ radialSq (approachingRay h) ≤ 5) ∧
    leadingScalar (approachingRay h) ≠ 0 ∧
    |cancellingAnnularRemainder h| ≤ (metricCoefficient : ℝ) * h ^ 5 ∧
    h ^ 4 * leadingScalar (approachingRay h) + cancellingAnnularRemainder h = 0) ∧
  (∀ (h d amplitude C : ℝ) (_hh : 0 < h) (_hd : 0 < d)
    (_ha : 0 < amplitude),
    amplitude ^ 2 / (h ^ 4 * d) ≤ C * amplitude ↔ amplitude ≤ C * h ^ 4 * d)
end Artform.Scores.GravityBridge.Statement
