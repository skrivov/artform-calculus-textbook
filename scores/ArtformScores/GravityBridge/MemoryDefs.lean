import ArtformScores.GravityBridge.LinearDefs

/-! # Two-block evolution with its auxiliary initial data retained -/

namespace Artform.Scores.GravityBridge

open Finset

variable {K Y Z : Type*} [Semiring K] [AddCommMonoid Y] [AddCommMonoid Z]
  [Module K Y] [Module K Z]

def blockStep (A : Y →ₗ[K] Y) (B : Z →ₗ[K] Y) (C : Y →ₗ[K] Z) (D : Z →ₗ[K] Z)
    (p : Y × Z) : Y × Z := (A p.1 + B p.2, C p.1 + D p.2)

def quarterTurn (p : ℚ × ℚ) : ℚ × ℚ := (p.2, -p.1)

def quarterVisible (n : ℕ) (x : ℚ) : ℚ := ((quarterTurn^[n]) (x, 0)).1

end Artform.Scores.GravityBridge
