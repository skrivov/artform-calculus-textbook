import ArtformScores.GravityBridge.KernelAlgebraStatements

/-! # Finite gluing is associative with the declared densities -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma weighted_compose_assoc {X Y Z W K : Type*} [Fintype Y] [Fintype Z] [CommSemiring K]
    (mu : Y → K) (nu : Z → K) (a : BoundaryKernel X Y K)
    (b : BoundaryKernel Y Z K) (c : BoundaryKernel Z W K) :
    weightedCompose nu (weightedCompose mu a b) c =
      weightedCompose mu a (weightedCompose nu b c) := by
  funext x w
  simp only [weightedCompose]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma weighted_left_unit {X Y K : Type*} [Fintype X] [Field K] (mu : X → K)
    (hmu : ∀ x, mu x ≠ 0) (a : BoundaryKernel X Y K) :
    weightedCompose mu (weightedUnit mu) a = a := by
  classical
  funext x y
  simp [weightedCompose, weightedUnit, hmu]

lemma weighted_right_unit {X Y K : Type*} [Fintype Y] [Field K] (mu : Y → K)
    (hmu : ∀ y, mu y ≠ 0) (a : BoundaryKernel X Y K) :
    weightedCompose mu a (weightedUnit mu) = a := by
  classical
  funext x y
  simp [weightedCompose, weightedUnit, hmu]

lemma full_left_unit_iff {X K : Type*} [Fintype X] [Field K] (mu : X → K) :
    (∃ e : BoundaryKernel X X K, ∀ a : BoundaryKernel X X K, weightedCompose mu e a = a) ↔
      ∀ x, mu x ≠ 0 := by
  classical
  constructor
  · rintro ⟨e, he⟩ x hx
    let delta : BoundaryKernel X X K := fun y z => if y = x ∧ z = x then 1 else 0
    have h := congrFun (congrFun (he delta) x) x
    simp [weightedCompose, delta, hx] at h
  · intro hmu
    exact ⟨weightedUnit mu, weighted_left_unit mu hmu⟩

/-- **GAC:weighted-kernel-algebra** (finite weighted composition and normalized units). -/
@[ledger "GAC:weighted-kernel-algebra"]
theorem kernelAlgebraLaw : Statement.kernelAlgebraLaw := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y Z W K _ _ _ mu nu a b c
    exact weighted_compose_assoc mu nu a b c
  · intro X Y K _ _ mu hmu a
    exact weighted_left_unit mu hmu a
  · intro X Y K _ _ mu hmu a
    exact weighted_right_unit mu hmu a
  · intro X K _ _ mu
    exact full_left_unit_iff mu

/-! ## Non-vacuity -/

example : weightedUnit (fun i : Fin 2 => if i = 0 then (1 : ℚ) else 2) 1 1 = 1 / 2 := by
  norm_num [weightedUnit]

example : ¬ ∃ e : BoundaryKernel (Fin 2) (Fin 2) ℚ,
    ∀ a : BoundaryKernel (Fin 2) (Fin 2) ℚ,
      weightedCompose (fun i : Fin 2 => if i = 0 then 1 else 0) e a = a := by
  rw [full_left_unit_iff]
  push Not
  exact ⟨1, by norm_num⟩

end

end Artform.Scores.GravityBridge
