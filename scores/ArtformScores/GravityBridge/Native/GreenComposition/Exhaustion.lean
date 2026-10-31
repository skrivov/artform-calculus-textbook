import ArtformScores.GravityBridge.Native.GreenComposition.ExhaustionStatements

/-! # Controlled L2 pair exhaustion with background separation -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {X : Type*}

open scoped BigOperators

lemma l2_pair_summable (f g : lp (fun _ : X => ℝ) 2) :
    Summable (fun n : X => f n * g n) := by
  have h := lp.summable_inner (𝕜 := ℝ) f g
  simpa only [Real.inner_apply] using h

lemma controlled_finite_exhaustion (f g : lp (fun _ : X => ℝ) 2) :
    Filter.Tendsto (fun s : Finset X => ∑ n ∈ s, f n * g n) Filter.atTop
      (nhds (∑' n : X, f n * g n)) :=
  (l2_pair_summable f g).hasSum

lemma full_space_background_not_summable : ¬ Summable (fun _ : ℤ => (1 : ℝ)) := by
  simp [summable_const_iff]

lemma fixed_h_finite_stencil_summable (I : Type) [Fintype I]
    (coeff : I → ℝ) (f g : I → lp (fun _ : X => ℝ) 2) :
    Summable (fun n : X => ∑ i, coeff i * (f i n * g i n)) := by
  exact summable_sum (fun i _ => (l2_pair_summable (f i) (g i)).mul_left (coeff i))

lemma nonzero_l2_seed : l2Seed 0 = 1 ∧ Summable (fun n : ℤ => l2Seed n * l2Seed n) := by
  constructor
  · simp [l2Seed]
  · exact l2_pair_summable _ _

/-- **GAC2:controlled-l2-current-exhaustion**
(controlled l2 pair exhaustion with background separation). -/
@[ledger "GAC2:controlled-l2-current-exhaustion"]
theorem exhaustionLaw : Statement.exhaustionLaw := by
  intro X
  exact ⟨l2_pair_summable,
    controlled_finite_exhaustion,
    full_space_background_not_summable,
    fixed_h_finite_stencil_summable,
    nonzero_l2_seed⟩

/-! ## Non-vacuity -/
example : Summable (fun n : ℤ => (0 : lp (fun _ : ℤ => ℝ) 2) n *
    (0 : lp (fun _ : ℤ => ℝ) 2) n) := l2_pair_summable 0 0

end Artform.Scores.GravityBridge.Native.GreenComposition
