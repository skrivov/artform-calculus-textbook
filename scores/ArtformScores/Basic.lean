import Mathlib
import ArtformScores.Meta.Ledger

/-!
# Scores and their laws

The syntax and the semantics of the algebra of scores (§1-§2 of the ledger's
`ALGEBRA-OF-SCORES.md`), for two channels `(b, e)` with values in a
commutative ring `S`, the stencil ring of the artform.

* A **step** is a kick `K f` (the shear `e += f b`) or a move `M f` (the shear
  `b += f e`), with a stencil `f : S`.
* A **score** is a list of steps in time order, the first step first.
* The **realizer** sends a score to its law in `SL(2, S)`: the later step acts
  after the earlier one, so `realize (w₁ ++ w₂) = realize w₂ * realize w₁`.
-/

namespace Artform.Scores

open Matrix (SpecialLinearGroup)

variable {S : Type*} [CommRing S]

/-- A step of the two-channel calculus: a kick `K f`, the shear `e += f b`, or
a move `M f`, the shear `b += f e`. -/
@[ledger "def:step"]
inductive Step (S : Type*) where
  | kick (f : S)
  | move (f : S)

/-- The matrix of a step, acting on the column `(b, e)`. -/
@[ledger "def:step"]
def Step.mat : Step S → Matrix (Fin 2) (Fin 2) S
  | .kick f => !![1, 0; f, 1]
  | .move f => !![1, f; 0, 1]

theorem Step.det_mat (s : Step S) : s.mat.det = 1 := by
  cases s <;> simp [Step.mat, Matrix.det_fin_two]

/-- A step as an element of `SL(2, S)`. -/
def Step.sl (s : Step S) : SpecialLinearGroup (Fin 2) S := ⟨s.mat, s.det_mat⟩

@[simp] theorem Step.coe_sl (s : Step S) :
    ((s.sl : SpecialLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) = s.mat := rfl

/-- The step with the opposite stencil, the inverse shear. -/
def Step.neg : Step S → Step S
  | .kick f => .kick (-f)
  | .move f => .move (-f)

/-- A score: its steps in time order, the first step first. -/
@[ledger "def:score"]
abbrev Score (S : Type*) := List (Step S)

/-- The realizer: the law of a score, each step acting after the ones before
it. -/
@[ledger "def:realizer"]
def realize : Score S → SpecialLinearGroup (Fin 2) S
  | [] => 1
  | s :: w => realize w * s.sl

/-- Time reversal of a score: the steps in the opposite order, each inverted. -/
@[ledger "def:time-reversal"]
def Score.reverse (w : Score S) : Score S := (w.map Step.neg).reverse

@[simp] theorem realize_nil : realize ([] : Score S) = 1 := rfl

@[simp] theorem realize_cons (s : Step S) (w : Score S) :
    realize (s :: w) = realize w * s.sl := rfl

theorem realize_append (w₁ w₂ : Score S) : realize (w₁ ++ w₂) = realize w₂ * realize w₁ := by
  induction w₁ with
  | nil => simp
  | cons s w ih => simp [ih, mul_assoc]

theorem realize_singleton (s : Step S) : realize [s] = s.sl := by simp

theorem Step.sl_neg (s : Step S) : s.neg.sl = s.sl⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  ext i j
  cases s <;> fin_cases i <;> fin_cases j <;>
    simp [Step.neg, Step.mat, Matrix.SpecialLinearGroup.coe_mul]

/-- The entries of a law: the phase is its trace, the reading its entry `a`. -/
def phase (T : SpecialLinearGroup (Fin 2) S) : S := (T : Matrix (Fin 2) (Fin 2) S).trace

/-- The reading of a law: the entry `a` of `T = [[a, b], [c, d]]`, the flux it
returns after one tick from `(b, e) = (1, 0)`. -/
def reading (T : SpecialLinearGroup (Fin 2) S) : S := (T : Matrix (Fin 2) (Fin 2) S) 0 0

/-- The Whitehead word of a unit `u`, the score `M(u) K(-u⁻¹) M(u)`. Its law is
`[[0, u], [-u⁻¹, 0]]`. -/
@[ledger "def:whitehead"]
def whitehead (u : Sˣ) : Score S := [.move ↑u, .kick (-↑u⁻¹), .move ↑u]

/-- The balanced pair of movers `h(u) = w(u) w(1)⁻¹`, the law `diag(u, u⁻¹)`. -/
@[ledger "def:balanced"]
def balanced (u : Sˣ) : SpecialLinearGroup (Fin 2) S :=
  realize (whitehead u) * (realize (whitehead 1))⁻¹

/-- The cut of a law, `a - d`: the difference of its diagonal entries. -/
@[ledger "def:cut"]
def cut {K : Type*} [Ring K] (T : Matrix (Fin 2) (Fin 2) K) : K := T 0 0 - T 1 1

/-- The one-mode tick of the leapfrog at pull `μ`: kick `K(1)`, then move
`M(-μ)`. -/
@[ledger "def:tick"]
def tick (μ : ℤ) : SpecialLinearGroup (Fin 2) ℤ := realize [.kick 1, .move (-μ)]

/-- The dimension split on one mode with pulls `gx`, `gy` and step `h`: the
score `K(h/4) M(-h gx) K(h/2) M(-h gy) K(h/4)`, or with `x` and `y`
exchanged when `xFirst` is false. -/
@[ledger "def:split"]
def splitTick {K : Type*} [Field K] (xFirst : Bool) (h gx gy : K) :
    SpecialLinearGroup (Fin 2) K :=
  let g₁ := if xFirst then gx else gy
  let g₂ := if xFirst then gy else gx
  realize [.kick (h / 4), .move (-(h * g₁)), .kick (h / 2), .move (-(h * g₂)), .kick (h / 4)]

end Artform.Scores
