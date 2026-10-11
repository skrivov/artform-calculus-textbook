import Mathlib.Basic.ENNReal.Inv
import ArtformTextbook.Meta.Book

/-!
# The exit law and recorded histories (Sections 4.6 to 4.8)

The caller's rule of Section 4.6 turns a uniform response pair into the exit
transition law `K(y | x)`, and Section 4.7 conditions on recorded exit
histories `X_0 = x_0, …, X_t = x_t`. Neither is a numbered definition of the
book; Proposition 4.4 uses both. The bits `B = {0, 1}` are `Fin 2`, where `+`
is addition modulo two and `*` is the product of two bits.
-/

namespace Artform

open scoped ENNReal

/-- The exit transition law `K(y | x)` of Section 4.6 (`prob:controller`). From
the old exit `x` the new exit `y` equals `x` with probability `3/4` and `1 - x`
with probability `1/4`. `exitTransition y x` is `K(y | x)`: the new exit first,
the old exit second, as in the book. -/
noncomputable def exitTransition (y x : Fin 2) : ℝ≥0∞ :=
  if y = x then 3 / 4 else 1 / 4

/-- The event that the process `X` shows the recorded values `h 0, …, h t` at
the times `0, …, t`: in the notation of Section 4.7,
`X_0 = x_0, …, X_t = x_t`. -/
def historyEvent {Ω α : Type*} (X : ℕ → Ω → α) (t : ℕ) (h : Fin (t + 1) → α) : Set Ω :=
  {ω | ∀ i : Fin (t + 1), X i ω = h i}

end Artform
