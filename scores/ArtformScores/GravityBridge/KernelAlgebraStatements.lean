import ArtformScores.GravityBridge.KernelAlgebraDefs

/-! # Weighted gluing and its true identity -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:weighted-kernel-algebra** (weighted gluing and its true identity). -/
@[ledger "GAC:weighted-kernel-algebra"]
def kernelAlgebraLaw : Prop :=
  (∀ (X Y Z W K : Type*) [Fintype Y] [Fintype Z] [CommSemiring K]
    (mu : Y → K) (nu : Z → K) (a : BoundaryKernel X Y K)
    (b : BoundaryKernel Y Z K) (c : BoundaryKernel Z W K),
    weightedCompose nu (weightedCompose mu a b) c =
      weightedCompose mu a (weightedCompose nu b c)) ∧
  (∀ (X Y K : Type*) [Fintype X] [Field K] (mu : X → K),
    (∀ x, mu x ≠ 0) → ∀ a : BoundaryKernel X Y K,
      weightedCompose mu (weightedUnit mu) a = a) ∧
  (∀ (X Y K : Type*) [Fintype Y] [Field K] (mu : Y → K),
    (∀ y, mu y ≠ 0) → ∀ a : BoundaryKernel X Y K,
      weightedCompose mu a (weightedUnit mu) = a) ∧
  (∀ (X K : Type*) [Fintype X] [Field K] (mu : X → K),
    (∃ e : BoundaryKernel X X K, ∀ a : BoundaryKernel X X K, weightedCompose mu e a = a) ↔
      ∀ x, mu x ≠ 0)

end Artform.Scores.GravityBridge.Statement
