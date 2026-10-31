import ArtformScores.GravityBridge.MemoryDefs

/-! # Declared linear sources and finite response experiments -/

namespace Artform.Scores.GravityBridge

open Finset Polynomial
variable {K X Y J : Type*} [Semiring K] [AddCommMonoid X] [AddCommMonoid Y]
  [AddCommMonoid J] [Module K X] [Module K Y] [Module K J]

def impulseResponse (O : X →ₗ[K] Y) (T : X →ₗ[K] X) (B : J →ₗ[K] X) (n : ℕ) (j : J) : Y :=
  O ((T ^ n) (B j))

def sourceAmplitude (O : X →ₗ[K] Y) (T : X →ₗ[K] X) (B : J →ₗ[K] X)
    (n : ℕ) (u : ℕ → J) : Y :=
  ∑ j ∈ range n, impulseResponse O T B (n - 1 - j) (u j)

def sourceShear : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) :=
  ((LinearMap.fst ℚ ℚ ℚ) + (LinearMap.snd ℚ ℚ ℚ)).prod (LinearMap.snd ℚ ℚ ℚ)

def auxiliaryInput : ℚ →ₗ[ℚ] (ℚ × ℚ) := (0 : ℚ →ₗ[ℚ] ℚ).prod LinearMap.id

def visibleOutput : (ℚ × ℚ) →ₗ[ℚ] ℚ := LinearMap.fst ℚ ℚ ℚ

end Artform.Scores.GravityBridge
