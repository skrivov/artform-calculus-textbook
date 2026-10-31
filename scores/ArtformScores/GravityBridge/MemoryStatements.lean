import ArtformScores.GravityBridge.MemoryDefs

/-! # Finite-time block memory and the precise preparation needed for closure -/

namespace Artform.Scores.GravityBridge.Statement

open Finset

/-- **GAC:block-memory** (exact memory and prepared autonomous graphs). -/
@[ledger "GAC:block-memory"]
def blockMemory : Prop :=
  (∀ (K Y Z : Type*) [Semiring K] [AddCommMonoid Y] [AddCommMonoid Z]
    [Module K Y] [Module K Z]
    (A : Y →ₗ[K] Y) (B : Z →ₗ[K] Y) (C : Y →ₗ[K] Z) (D : Z →ₗ[K] Z)
    (x : ℕ → Y) (z : ℕ → Z),
    (∀ n, x (n + 1) = A (x n) + B (z n)) →
    (∀ n, z (n + 1) = C (x n) + D (z n)) → ∀ n,
      z n = (D ^ n) (z 0) + ∑ j ∈ range n, (D ^ (n - 1 - j)) (C (x j)) ∧
      x (n + 1) = A (x n) + B ((D ^ n) (z 0)) +
        ∑ j ∈ range n, B ((D ^ (n - 1 - j)) (C (x j)))) ∧
  (∀ (K Y Z : Type*) [Semiring K] [AddCommMonoid Y] [AddCommMonoid Z]
    [Module K Y] [Module K Z]
    (A : Y →ₗ[K] Y) (B : Z →ₗ[K] Y) (C : Y →ₗ[K] Z) (D : Z →ₗ[K] Z)
    (J : Y →ₗ[K] Z),
    (∀ y, C y + D (J y) = J (A y + B (J y))) → ∀ (n : ℕ) (y : Y),
      ((blockStep A B C D)^[n]) (y, J y) =
        (((fun x => A x + B (J x))^[n]) y,
          J (((fun x => A x + B (J x))^[n]) y))) ∧
  (∀ (K Y Z : Type*) [Semiring K] [AddCommMonoid Y] [AddCommMonoid Z]
    [Module K Y] [Module K Z] (A : Y →ₗ[K] Y) (B : Z →ₗ[K] Y),
    (∃ U : Y → Y, ∀ x z, A x + B z = U x) ↔ B = 0) ∧
  (¬ ∃ U : ℚ → ℚ, ∀ (x : ℚ) (n : ℕ),
    quarterVisible (n + 1) x = U (quarterVisible n x))

end Artform.Scores.GravityBridge.Statement
