import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Defs
import ArtformTextbook.Meta.Book

/-!
# Five kinds of equation (*What kind of statement is an equation?*)

Definition 5.14 sorts equations into five kinds. In Lean the five kinds are
five kinds of declaration, and the book's five examples, on the corners
`v₀, …, v₃` of the square (`ZMod 4`), are written each in its own kind:

* a definition introduces a symbol: `zeros p`, the number of zeros of `p`;
* an identity follows from prior structure, and is a theorem:
  `Σᵢ (p(vᵢ) - p(vᵢ₋₁)) = 0` around the square (`squareIdentity`), which holds
  of every table (`squareIdentity_holds`);
* an invariant constraint selects legal states: the walker's
  `p(v₀) + p(v₁) + p(v₂) + p(v₃) = 1`, among the tables of zeros and ones
  (`walkerConstraint`);
* an evolution rule maps one state to another: `p'(vᵢ) = p(vᵢ₋₁)`
  (`walkerTick`);
* a recognizer tests a pattern: `p₂ = p₀`, with `p_t` the state after `t`
  ticks, true exactly when opposite corners agree (`oppositeAgree`,
  `oppositeAgree_iff`).
-/

namespace Artform

/-- **Definition 5.14** (five kinds of equation): what an equation may be. -/
@[book "def:equation-roles"]
inductive EquationRole where
  /-- It introduces a symbol. -/
  | definition
  /-- It follows from prior structure. -/
  | identity
  /-- It selects legal states. -/
  | invariantConstraint
  /-- It maps one state to another. -/
  | evolutionRule
  /-- It tests a pattern or an observable. -/
  | recognizer
  deriving DecidableEq

namespace FiveEquations

/-- **Definition 5.14** (a definition): `z(p) :=` the number of zeros of `p`. -/
@[book "def:equation-roles"]
def zeros (p : ZMod 4 → ℤ) : ℕ := (Finset.univ.filter fun i => p i = 0).card

/-- **Definition 5.14** (an identity): `Σᵢ (p(vᵢ) - p(vᵢ₋₁)) = 0` around the
square. As an equation it holds of every table `p` (`squareIdentity_holds`). -/
@[book "def:equation-roles"]
def squareIdentity (p : ZMod 4 → ℤ) : Prop := ∑ i, (p i - p (i - 1)) = 0

/-- The identity follows from prior structure: around the square every value
is added once and taken away once. -/
theorem squareIdentity_holds (p : ZMod 4 → ℤ) : squareIdentity p := by
  rw [squareIdentity, Finset.sum_sub_distrib, sub_eq_zero]
  exact (Equiv.sum_comp (Equiv.subRight (1 : ZMod 4)) p).symm

/-- **Definition 5.14** (an invariant constraint): the walker's
`p(v₀) + p(v₁) + p(v₂) + p(v₃) = 1`, a sum of integers, which selects the legal
states among the tables of zeros and ones. -/
@[book "def:equation-roles"]
def walkerConstraint (p : ZMod 4 → Fin 2) : Prop := ∑ i, ((p i : ℕ) : ℤ) = 1

instance : DecidablePred walkerConstraint := fun p => by
  unfold walkerConstraint
  infer_instance

/-- **Definition 5.14** (an evolution rule): `p'(vᵢ) = p(vᵢ₋₁)`. -/
@[book "def:equation-roles"]
def walkerTick {α : Type*} (p : ZMod 4 → α) : ZMod 4 → α := fun i => p (i - 1)

/-- **Definition 5.14** (a recognizer): `p₂ = p₀`, with `p_t` the state after `t`
ticks. -/
@[book "def:equation-roles"]
def oppositeAgree {α : Type*} (p : ZMod 4 → α) : Prop := walkerTick (walkerTick p) = p

/-- The recognizer is true exactly when opposite corners agree. -/
theorem oppositeAgree_iff {α : Type*} (p : ZMod 4 → α) :
    oppositeAgree p ↔ ∀ i, p (i + 2) = p i := by
  constructor
  · intro h i
    have := congrFun h (i + 2)
    simpa [walkerTick, sub_sub, show (1 : ZMod 4) + 1 = 2 from rfl] using this.symm
  · intro h
    funext i
    have := h (i - 2)
    simpa [walkerTick, sub_sub, show (1 : ZMod 4) + 1 = 2 from rfl] using this.symm

/-- The kind of each of the book's five examples. -/
def role : Fin 5 → EquationRole :=
  ![.definition, .identity, .invariantConstraint, .evolutionRule, .recognizer]

/-! ## Non-vacuity -/

/-- The walker's evolution rule keeps its invariant constraint: one token stays
one token. -/
example (p : ZMod 4 → Fin 2) (h : walkerConstraint p) : walkerConstraint (walkerTick p) := by
  revert h
  revert p
  decide

end FiveEquations

end Artform
