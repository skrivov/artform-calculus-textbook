import ArtformStages.Pair

/-!
# Pair with a drift by sorts

When the drift has one weight for each sort of line, `L = D D` with `D` its square root, and
the scaling `A ↦ D⁻¹ A`, `E ↦ D E` turns Pair into a Pair whose drift is `1`: the window of a
board whose weights read the paint is the window of the kick `D S D`. And a level of the pair
`(S, L)`, a `v` with `L S v = μ v`, carries the Pair of one place with `σ = 1` and `λ = μ`.
This is road DP's campaign 4 in the research ledger on a layered universe.

* `scale`, `pair_scale` (WS1), `omega_scale` (WS2), `pair_on_pair_level` (WS3).
-/

open Matrix

namespace Artform.Stages

section Scale

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n]

/-- The scaling: the lines by `D'`, the dual lines by `D`. -/
def scale (D D' : Matrix n n R) (x : LightState R n) : LightState R n := (D' *ᵥ x.1, D *ᵥ x.2)

theorem scale_dotProduct [DecidableEq n] (M N : Matrix n n R) (h : Nᵀ * M = 1) (v w : n → R) :
    (M *ᵥ v) ⬝ᵥ (N *ᵥ w) = v ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, h, one_mulVec]

/-- WS1. With `D D' = D' D = 1`, Pair with the drift `D D`, scaled, is Pair with the kick
`D S D` and the drift `1` at the scaled state. -/
theorem pair_scale [DecidableEq n] (D D' S : Matrix n n R) (h1 : D * D' = 1) (h2 : D' * D = 1)
    (x : LightState R n) :
    scale D D' (pair S (D * D) x) = pair (D * S * D) 1 (scale D D' x) := by
  obtain ⟨A, E⟩ := x
  have hk : (D * S * D) *ᵥ (D' *ᵥ A) = D *ᵥ (S *ᵥ A) := by
    rw [mulVec_mulVec, Matrix.mul_assoc (D * S), h1, Matrix.mul_one, ← mulVec_mulVec]
  have hd : ∀ w : n → R, D' *ᵥ ((D * D) *ᵥ w) = D *ᵥ w := fun w => by
    rw [mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [scale, pair, mulVec_sub, hd, hk, one_mulVec, mulVec_add]

/-- WS2. With `D` and `D'` symmetric, the scaling keeps the alternating pairing. -/
theorem omega_scale [DecidableEq n] (D D' : Matrix n n R) (h1 : D * D' = 1) (h2 : D' * D = 1)
    (hD : Dᵀ = D) (hD' : D'ᵀ = D') (x y : LightState R n) :
    omega (scale D D' x) (scale D D' y) = omega x y := by
  have e1 : Dᵀ * D' = 1 := by rw [hD]; exact h1
  have e2 : D'ᵀ * D = 1 := by rw [hD']; exact h2
  simp only [omega, scale, scale_dotProduct D' D e1, scale_dotProduct D D' e2]

/-- WS3. On a level of the pair `(S, L)`, `L S v = μ v`, Pair is the Pair of one place with
`σ = 1` and `λ = μ`: `e' = e + a`, `a' = a - μ e'`. -/
theorem pair_on_pair_level (S L : Matrix n n R) (v : n → R) (μ : R)
    (hv : L *ᵥ (S *ᵥ v) = μ • v) (a e : R) :
    pair S L (a • v, e • (S *ᵥ v)) = ((a - μ * (e + a)) • v, (e + a) • (S *ᵥ v)) := by
  have h1 : S *ᵥ (a • v) = a • (S *ᵥ v) := mulVec_smul S a v
  have h2 : L *ᵥ ((e + a) • (S *ᵥ v)) = ((e + a) * μ) • v := by rw [mulVec_smul, hv, smul_smul]
  simp only [pair, h1]
  rw [← add_smul, h2]
  ext i <;> simp
  ring

end Scale

end Artform.Stages
