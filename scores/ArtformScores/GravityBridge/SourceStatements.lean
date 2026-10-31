import ArtformScores.GravityBridge.SourceDefs

/-! # Declared finite source responses and a separating experiment -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:source-response** (all impulse coefficients characterize declared finite experiments). -/
@[ledger "GAC:source-response"]
def sourceResponse : Prop :=
  (∀ (K X Y J : Type*) [Semiring K] [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid J]
    [Module K X] [Module K Y] [Module K J]
    (O : X →ₗ[K] Y) (T : X →ₗ[K] X) (B : J →ₗ[K] X) (x : ℕ → X) (u : ℕ → J),
    x 0 = 0 → (∀ n, x (n + 1) = T (x n) + B (u n)) →
      ∀ n, O (x n) = sourceAmplitude O T B n u) ∧
  (∀ (K X X' Y J : Type*) [Semiring K] [AddCommMonoid X] [AddCommMonoid X']
    [AddCommMonoid Y] [AddCommMonoid J] [Module K X] [Module K X'] [Module K Y] [Module K J]
    (O1 : X →ₗ[K] Y) (O2 : X' →ₗ[K] Y) (T1 : X →ₗ[K] X) (T2 : X' →ₗ[K] X')
    (B1 : J →ₗ[K] X) (B2 : J →ₗ[K] X'),
    ((∀ n j, impulseResponse O1 T1 B1 n j = impulseResponse O2 T2 B2 n j) ↔
      ∀ n u, sourceAmplitude O1 T1 B1 n u = sourceAmplitude O2 T2 B2 n u)) ∧
  (Step.move (1 : ℚ)).mat.charpoly = (1 : Matrix (Fin 2) (Fin 2) ℚ).charpoly ∧
  (∀ (n : ℕ) (x : ℚ), (sourceShear ^ n) (x, 0) = (x, 0)) ∧
  impulseResponse visibleOutput sourceShear auxiliaryInput 1 1 = 1 ∧
  impulseResponse visibleOutput LinearMap.id auxiliaryInput 1 1 = 0

end Artform.Scores.GravityBridge.Statement
