import ArtformScores.GravityBridge.Native.GreenComposition.ExhaustionDefs

/-! # Controlled L2 pair exhaustion with background separation -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition.Statement

open scoped BigOperators

/-- **GAC2:controlled-l2-current-exhaustion**
(controlled l2 pair exhaustion with background separation). -/
@[ledger "GAC2:controlled-l2-current-exhaustion"]
def exhaustionLaw : Prop :=
  ∀ (X : Type),
    (∀ (f g : lp (fun _ : X => ℝ) 2),
    Summable (fun n : X => f n * g n)) ∧
    (∀ (f g : lp (fun _ : X => ℝ) 2),
    Filter.Tendsto (fun s : Finset X => ∑ n ∈ s, f n * g n) Filter.atTop
      (nhds (∑' n : X, f n * g n))) ∧
    (¬ Summable (fun _ : ℤ => (1 : ℝ))) ∧
    (∀ (I : Type) [Fintype I]
    (coeff : I → ℝ) (f g : I → lp (fun _ : X => ℝ) 2),
    Summable (fun n : X => ∑ i, coeff i * (f i n * g i n))) ∧
    (l2Seed 0 = 1 ∧ Summable (fun n : ℤ => l2Seed n * l2Seed n))

end Artform.Scores.GravityBridge.Native.GreenComposition.Statement
