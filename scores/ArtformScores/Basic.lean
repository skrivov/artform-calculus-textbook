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


/-! ## The one-mode presentation

On one mode over `ZMod p` every stencil is a constant, and every step is a power of
the move `X = M(1)` or of the kick `Y = K(1)`: `M(f) = X^f` and `K(f) = Y^f`, with
`0 ≤ f < p`. The rules R1 and R3, read as words in `X` and `Y`, are the relators of
a presented group (T4). -/

namespace OneMode

/-- The generators of the one-mode presentation: the move `X = M(1)` and the kick
`Y = K(1)`. -/
@[ledger "def:one-mode"]
inductive Gen
  | X
  | Y
  deriving DecidableEq

/-- The word of the move `M(f) = X^f`, with `0 ≤ f < p`. -/
@[ledger "def:one-mode"]
def move (p : ℕ) (f : ZMod p) : FreeGroup Gen := FreeGroup.of .X ^ f.val

/-- The word of the kick `K(f) = Y^f`, with `0 ≤ f < p`. -/
@[ledger "def:one-mode"]
def kick (p : ℕ) (f : ZMod p) : FreeGroup Gen := FreeGroup.of .Y ^ f.val

/-- The word of the Whitehead score `w(u) = M(u) K(-u⁻¹) M(u)`. -/
@[ledger "def:one-mode"]
def whiteheadWord (p : ℕ) (u : (ZMod p)ˣ) : FreeGroup Gen :=
  move p ↑u * kick p (-↑u⁻¹) * move p ↑u

/-- The relators of merging (R1), `M(f) M(g) = M(f + g)` and `K(f) K(g) = K(f + g)`,
and of Whitehead's rule (R3), `w(u) M(f) w(u)⁻¹ = K(-u⁻² f)` and
`w(u) K(f) w(u)⁻¹ = M(-u² f)`, for all stencils `f`, `g` and units `u` of `ZMod p`. -/
@[ledger "def:one-mode"]
def relators (p : ℕ) : Set (FreeGroup Gen) :=
  {r | ∃ f g : ZMod p, r = move p f * move p g * (move p (f + g))⁻¹ ∨
      r = kick p f * kick p g * (kick p (f + g))⁻¹} ∪
  {r | ∃ (u : (ZMod p)ˣ) (f : ZMod p),
      r = whiteheadWord p u * move p f * (whiteheadWord p u)⁻¹ *
        (kick p (-(↑u⁻¹ * ↑u⁻¹ * f)))⁻¹ ∨
      r = whiteheadWord p u * kick p f * (whiteheadWord p u)⁻¹ *
        (move p (-(↑u * ↑u * f)))⁻¹}

/-- The law of a word: `X` is the move `M(1)` and `Y` the kick `K(1)`. -/
@[ledger "def:one-mode"]
def law (p : ℕ) : FreeGroup Gen →* SpecialLinearGroup (Fin 2) (ZMod p) :=
  FreeGroup.lift fun
    | .X => (Step.move 1).sl
    | .Y => (Step.kick 1).sl

end OneMode


/-! ## Blocking

Blocking by a sublattice `Λ′ ⊂ Λ` of index `m` (the ledger's §1, Definition 3) reads the
artform `A` as an artform `B(A)` with `2m` channels. The stencil ring `S = R[Λ]` is a free
module over `S′ = R[Λ′]`, with one basis vector for each coset of `Λ′`: the *places*. The
channel `(i, s)` of `B(A)` is the channel `i` of `A` at the place `s`, and a stencil `f`
of `A` acts on the places by the matrix of multiplication by `f`
(`Algebra.leftMulMatrix`). -/

section Blocking

variable {S' : Type*} [CommRing S'] {m : ℕ}

/-- The blocking `B(T)` of a law `T` of `A`: the law on the `2m` channels of `B(A)` whose
entry `((i, s), (j, t))` is the entry `(s, t)` of the matrix of `T i j`. -/
@[ledger "def:block"]
noncomputable def block [Algebra S' S] (bs : Module.Basis (Fin m) S' S)
    (T : Matrix (Fin 2) (Fin 2) S) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) S' :=
  Matrix.of fun p q => Algebra.leftMulMatrix bs (T p.1 q.1) p.2 q.2

/-- A placed step of `B(A)`: add `g` times the channel `β` to the channel `α`. -/
@[ledger "def:block"]
structure PStep (S' : Type*) (m : ℕ) where
  α : Fin 2 × Fin m
  β : Fin 2 × Fin m
  g : S'

/-- The law of a placed step, the shear `1 + g E_αβ`. -/
@[ledger "def:block"]
def PStep.mat (s : PStep S' m) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) S' :=
  1 + Matrix.single s.α s.β s.g

/-- The law of a score of placed steps, in time order as for `realize`. -/
@[ledger "def:block"]
def realizePlaced : List (PStep S' m) → Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) S'
  | [] => 1
  | s :: w => realizePlaced w * s.mat

/-- The placed steps of a blocked step. The kick `K(f)` adds `B(f)_st` times `b` at the
place `t` to `e` at the place `s`, for all places `s` and `t`; the move `M(f)` adds from
`e` to `b` in the same way. -/
@[ledger "def:block"]
noncomputable def Step.block [Algebra S' S] (bs : Module.Basis (Fin m) S' S) :
    Step S → List (PStep S' m)
  | .kick f => (List.finRange m).flatMap fun s => (List.finRange m).map fun t =>
      ⟨(1, s), (0, t), Algebra.leftMulMatrix bs f s t⟩
  | .move f => (List.finRange m).flatMap fun s => (List.finRange m).map fun t =>
      ⟨(0, s), (1, t), Algebra.leftMulMatrix bs f s t⟩

/-- The blocked score `B(w)`: each step replaced by its placed steps. -/
@[ledger "def:block"]
noncomputable def blockScore [Algebra S' S] (bs : Module.Basis (Fin m) S' S) (w : Score S) :
    List (PStep S' m) :=
  w.flatMap (Step.block bs)

/-- On an index-2 blocking, with the places red (`0`) and black (`1`): the red kick,
`e += κ b` at the red places only. -/
@[ledger "def:red-black"]
def redKick (κ : S') : PStep S' 2 := ⟨(1, 0), (0, 0), κ⟩

/-- The black kick, `e += κ b` at the black places only. -/
@[ledger "def:red-black"]
def blackKick (κ : S') : PStep S' 2 := ⟨(1, 1), (0, 1), κ⟩

/-- The red-black tick (the ledger's finding 044): the red kick `K_red(κ)`, the move
`M(h)`, the black kick `K_black(κ)`, and the move `M(h)` again. -/
@[ledger "def:red-black"]
noncomputable def redBlackTick [Algebra S' S] (bs : Module.Basis (Fin 2) S' S) (κ : S') (h : S) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) S' :=
  realizePlaced ([redKick κ] ++ (Step.move h).block bs ++ [blackKick κ] ++ (Step.move h).block bs)

/-- The black-red tick: the same, with the black kick first. -/
@[ledger "def:red-black"]
noncomputable def blackRedTick [Algebra S' S] (bs : Module.Basis (Fin 2) S' S) (κ : S') (h : S) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) S' :=
  realizePlaced ([blackKick κ] ++ (Step.move h).block bs ++ [redKick κ] ++ (Step.move h).block bs)

end Blocking

end Artform.Scores
