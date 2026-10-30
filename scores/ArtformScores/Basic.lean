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


/-! ## Blocking by a sublattice

The stencils of a lattice `Λ` are its group ring `R[Λ]`, and those of a sublattice `Λ′` are
`R[Λ′] ⊂ R[Λ]` (the ledger's Definition 3). On `ℤ²` the red-black scheme blocks by the
checkerboard: the red cells `(a, b)` have `a + b` even, the black ones `a + b` odd. -/

section Sublattice

/-- The stencils of a sublattice `Λ′ ⊂ Λ` act on those of `Λ`, `R[Λ′] ⊂ R[Λ]`: a shift by a
cell of `Λ′` is a shift of `Λ`. -/
@[ledger "def:block"]
noncomputable instance sublatticeAlgebra {R Λ : Type*} [CommRing R] [AddCommGroup Λ]
    (Λ' : AddSubgroup Λ) : Algebra (AddMonoidAlgebra R Λ') (AddMonoidAlgebra R Λ) :=
  (AddMonoidAlgebra.mapDomainRingHom R Λ'.subtype).toAlgebra

/-- The checkerboard: the cells `(a, b)` of `ℤ²` with `a + b` even, the red cells. -/
@[ledger "def:red-black"]
def checkerboard : AddSubgroup (ℤ × ℤ) where
  carrier := {p | (p.1 + p.2) % 2 = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at *
    omega
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg] at *
    omega

/-- The cell `u = (1, 1)` of the checkerboard, the shift `x y`. -/
@[ledger "def:red-black"]
def cellU : checkerboard := ⟨(1, 1), by change ((1 : ℤ) + 1) % 2 = 0; decide⟩

/-- The cell `v = (1, -1)` of the checkerboard, the shift `x/y`. -/
@[ledger "def:red-black"]
def cellV : checkerboard := ⟨(1, -1), by change ((1 : ℤ) + -1) % 2 = 0; decide⟩

/-- The shift `x` of `ℤ²` by `e₁`, a stencil of the plane `R[x^±1, y^±1] = R[ℤ²]`. -/
@[ledger "def:red-black"]
noncomputable def shiftX (R : Type*) [CommRing R] : AddMonoidAlgebra R (ℤ × ℤ) :=
  AddMonoidAlgebra.single (1, 0) 1

/-- The book's face form in the plane, `g = 4 - x - 1/x - y - 1/y` (the ledger's
Definition 2). -/
@[ledger "def:face-form"]
noncomputable def faceStencil (R : Type*) [CommRing R] : AddMonoidAlgebra R (ℤ × ℤ) :=
  4 - AddMonoidAlgebra.single (1, 0) 1 - AddMonoidAlgebra.single (-1, 0) 1 -
    AddMonoidAlgebra.single (0, 1) 1 - AddMonoidAlgebra.single (0, -1) 1

end Sublattice


/-! ## The curve of a phase

A law `T = [[a, b], [c, d]]` of phase `t` acts on the curve `λ + 1/λ = t`, the dispersion
relation, whose ring is `A_t = S[λ]/(λ² - tλ + 1)` (the ledger's T7 and finding 057). The
row `u = (c, λ - a)` is a left eigenvector of `T`, and the ideal `(c, λ - a)` of `A_t` is
the law's class. -/

section Curve

/-- The ring of the curve of the phase `t`, `A_t = S[λ]/(λ² - tλ + 1)`. -/
@[ledger "def:curve"]
abbrev curveRing (t : S) :=
  AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1 : Polynomial S)

/-- The tick's eigenvalue `λ` on the curve. -/
@[ledger "def:curve"]
noncomputable def eig (t : S) : curveRing t := AdjoinRoot.root _

/-- The left eigenvector `u = (c, λ - a)` of a law `[[a, b], [c, d]]` on the curve. -/
@[ledger "def:curve"]
noncomputable def eigenRow (t : S) (T : Matrix (Fin 2) (Fin 2) S) : Fin 2 → curveRing t :=
  ![algebraMap S (curveRing t) (T 1 0), eig t - algebraMap S (curveRing t) (T 0 0)]

/-- The ideal `(c, λ - a)` of a law on the curve of `t`. -/
@[ledger "def:curve"]
noncomputable def lawIdeal (t : S) (T : Matrix (Fin 2) (Fin 2) S) : Ideal (curveRing t) :=
  Ideal.span {algebraMap S (curveRing t) (T 1 0), eig t - algebraMap S (curveRing t) (T 0 0)}

/-- Two ideals in the same class: `α I = β J` for non-zero-divisors `α` and `β`, so that
`I` and `J` differ by a factor of the ring of fractions. -/
@[ledger "def:curve"]
def SameClass {A : Type*} [CommRing A] (I J : Ideal A) : Prop :=
  ∃ α ∈ nonZeroDivisors A, ∃ β ∈ nonZeroDivisors A, Ideal.span {α} * I = Ideal.span {β} * J

/-- `t² - 4` is not a square in the fraction field: `y² = (t² - 4) z²` forces `z = 0`. -/
@[ledger "def:curve"]
def NonSquareDisc (t : S) : Prop := ∀ y z : S, y * y = (t * t - 4) * (z * z) → z = 0

/-- The matrix `[v | T v]` of a vector and its image. Its determinant is
`c v₀² + (d - a) v₀ v₁ - b v₁²`, the law's quadratic form. -/
@[ledger "def:curve"]
def cyclicMatrix (T : Matrix (Fin 2) (Fin 2) S) (v : Fin 2 → S) : Matrix (Fin 2) (Fin 2) S :=
  !![v 0, (T.mulVec v) 0; v 1, (T.mulVec v) 1]

/-- The companion tick `[[0, -1], [1, t]]` of the phase `t`, the recurrence
`u(n + 1) + u(n - 1) = t u(n)` on one channel. -/
@[ledger "def:curve"]
def companion (t : S) : Matrix (Fin 2) (Fin 2) S := !![0, -1; 1, t]

end Curve


/-! ## Bells

Change ringing on `N` bells (the ledger's T15 and finding 042). The positions are
`0, …, N - 1`, the front first. A *change* swaps disjoint pairs of neighbours, and the other
bells make places. Painting a number on each bell reads a row as a field: the number on the
bell in each position. -/

namespace Bells

open Equiv

variable {N : ℕ}

/-- A change: an involution of the positions that moves each position at most one place, so
a product of disjoint swaps of neighbours. -/
@[ledger "def:change"]
def IsChange (π : Perm (Fin N)) : Prop :=
  ∀ i, π (π i) = i ∧ (π i : ℕ) ≤ i + 1 ∧ (i : ℕ) ≤ π i + 1

/-- A change acting on a painted row: `(P_π u) i = u (π i)`. -/
@[ledger "def:change"]
def act {R : Type*} (π : Perm (Fin N)) (u : Fin N → R) : Fin N → R := fun i => u (π i)

/-- The rows of a method, the changes `π 0, π 1, …` rung in turn from rounds: `row π t b` is
the position of the bell `b` after `t` changes. -/
@[ledger "def:change"]
def row (π : ℕ → Perm (Fin N)) : ℕ → Perm (Fin N)
  | 0 => 1
  | t + 1 => π t * row π t

/-- A row painted by `f`, a number on each bell: the number on the bell in each position. -/
@[ledger "def:change"]
def paint {R : Type*} (f : Fin N → R) (σ : Perm (Fin N)) : Fin N → R := fun i => f (σ.symm i)

/-- The changes `A` and `B` dodge at `i`: both swap `i` with the same neighbour. -/
@[ledger "def:box"]
def IsDodge (A B : Perm (Fin N)) (i : Fin N) : Prop := A i = B i ∧ A i ≠ i

/-- The left neighbour of `i` in the box that the changes `A` and `B` cut: `i - 1` if one of
them swaps the two, else `i` itself, a wall. -/
@[ledger "def:box"]
def boxLeft (A B : Perm (Fin N)) (i : Fin N) : Fin N :=
  if (A i : ℕ) + 1 = i then A i else if (B i : ℕ) + 1 = i then B i else i

/-- The right neighbour of `i` in its box: `i + 1` if one of the changes swaps the two, else
`i` itself, a wall. -/
@[ledger "def:box"]
def boxRight (A B : Perm (Fin N)) (i : Fin N) : Fin N :=
  if (A i : ℕ) = i + 1 then A i else if (B i : ℕ) = i + 1 then B i else i

/-- The neighbour sum of the boxes that `A` and `B` cut, with a mirror at each wall. -/
@[ledger "def:box"]
def boxSum {R : Type*} [Add R] (A B : Perm (Fin N)) (u : Fin N → R) : Fin N → R :=
  fun i => u (boxLeft A B i) + u (boxRight A B i)

/-- The neighbour sum of the mirror box, `(S u) i = u (i - 1) + u (i + 1)`, with the ghosts
`u (-1) = u 0` and `u N = u (N - 1)`. -/
@[ledger "def:box"]
def mirror {R : Type*} [Add R] (u : Fin N → R) : Fin N → R := fun i =>
  u ⟨i - 1, by have := i.2; omega⟩ + u ⟨min (i + 1) (N - 1), by have := i.2; omega⟩

/-- The partner of the position `i` in the change that swaps the pairs `(2j + e, 2j + e + 1)`,
with `e` taken mod 2. -/
@[ledger "def:plain-hunt"]
def partner (N e i : ℕ) : ℕ :=
  if i % 2 = e % 2 then (if i + 1 < N then i + 1 else i) else i - 1

/-- The change that swaps the pairs `(2j + e, 2j + e + 1)`; a bell with no partner makes a
place. -/
@[ledger "def:plain-hunt"]
def huntChange (N e : ℕ) : Perm (Fin N) :=
  Function.Involutive.toPerm
    (fun i => ⟨partner N e i, by have := i.2; unfold partner; split_ifs <;> omega⟩)
    (fun i => Fin.ext (by
      have := i.2
      change partner N e (partner N e i) = i
      unfold partner
      split_ifs <;> omega))

/-- Plain hunt's cross, `X = (12)(34)…` in the ledger's numbering from 1. -/
@[ledger "def:plain-hunt"]
def huntX (N : ℕ) : Perm (Fin N) := huntChange N 0

/-- Plain hunt's other change, `Y = (23)(45)…`. -/
@[ledger "def:plain-hunt"]
def huntY (N : ℕ) : Perm (Fin N) := huntChange N 1

/-- The rows of plain hunt: `X` and `Y` in turn, `X` first. -/
@[ledger "def:plain-hunt"]
def hunt (N : ℕ) : ℕ → Perm (Fin N) := row (huntChange N)

/-- The mirror: the point `k` of a circle of `2N` places, folded onto the box `0, …, N - 1`. -/
@[ledger "def:plain-hunt"]
def fold (N k : ℕ) : ℕ := if k % (2 * N) < N then k % (2 * N) else 2 * N - 1 - k % (2 * N)

/-- The starting point on the circle of the bell in the position `b`: a bell in an even
position sets off up, one in an odd position down. -/
@[ledger "def:plain-hunt"]
def start (N b : ℕ) : ℕ := if b % 2 = 0 then b else 2 * N - 1 - b

/-- The mode `k` of the mirror box, `v_k(i) = cos(πk(2i + 1)/(2N))`. -/
@[ledger "def:mode"]
noncomputable def mode (N k : ℕ) : Fin N → ℝ := fun i =>
  Real.cos (Real.pi * k * (2 * i + 1) / (2 * N))

/-- The mode `k` turned by `πk/N` per change: `(A cos(πkt/N) + B sin(πkt/N)) v_k`. -/
@[ledger "def:mode"]
noncomputable def turn (N k : ℕ) (A B : ℝ) (t : ℕ) : Fin N → ℝ :=
  (A * Real.cos (Real.pi * k / N * t) + B * Real.sin (Real.pi * k / N * t)) • mode N k

/-- The law of a word in the generators `s_i`, the swaps of the neighbours `i` and `i + 1` of
`n + 1` positions. -/
@[ledger "def:bells-law"]
def law (n : ℕ) : FreeGroup (Fin n) →* Perm (Fin (n + 1)) :=
  FreeGroup.lift fun i => swap i.castSucc i.succ

/-- An extent of a group `G` under the steps `A` and `B` (the ledger's finding 043): a run
`x → A x` or `x → B x` that visits every element once and comes back, a Hamiltonian cycle of
the Cayley digraph. As a permutation `σ`, each `σ x` is `A x` or `B x`, and the powers of `σ`
carry any element to any other. -/
@[ledger "def:extent"]
def IsExtent {G : Type*} [Group G] (A B : G) (σ : Perm G) : Prop :=
  (∀ x, σ x = A * x ∨ σ x = B * x) ∧ ∀ x y, ∃ k : ℕ, (σ ^ k) x = y

/-- The Fibonacci rank of apparition `α(p)`: the least `k ≥ 1` with `p ∣ F_k`. -/
@[ledger "def:extent"]
noncomputable def fibRank (p : ℕ) : ℕ := sInf {k | 0 < k ∧ p ∣ Nat.fib k}

/-- The subgroup `{±1}` of `SL(2, Z/n)`, by which `PSL(2, Z/n) = SL(2, Z/n)/{±1}`, the groups of
the ledger's findings 037, 038 and 043. -/
@[ledger "def:extent"]
def pmOne (n : ℕ) : Subgroup (SpecialLinearGroup (Fin 2) (ZMod n)) := Subgroup.zpowers (-1)

/-- `{±1}` is central, so normal. -/
@[ledger "def:extent"]
instance pmOne_normal (n : ℕ) : (pmOne n).Normal where
  conj_mem a ha g := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [((Commute.neg_one_right g).zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ _

/-- A run of a group `G` under the steps `A` and `B`, with back-steps allowed (finding 043): a
permutation `σ` through all of `G`, each `σ x` being `A x`, `B x`, `A⁻¹ x` or `B⁻¹ x`. An extent is
a run with no back-steps. -/
@[ledger "def:extent"]
def IsRun {G : Type*} [Group G] (A B : G) (σ : Perm G) : Prop :=
  (∀ x, σ x = A * x ∨ σ x = B * x ∨ σ x = A⁻¹ * x ∨ σ x = B⁻¹ * x) ∧ ∀ x y, ∃ k : ℕ, (σ ^ k) x = y

/-- The back-steps of a permutation `σ`: the elements that it moves by neither `A` nor `B`. -/
@[ledger "def:extent"]
def backSteps {G : Type*} [Group G] (A B : G) (σ : Perm G) : Set G :=
  {x | σ x ≠ A * x ∧ σ x ≠ B * x}

/-- The fewest back-steps of a run of `G` under `A` and `B` is `k`: some run has `k`, and none has
fewer. -/
@[ledger "def:extent"]
def FewestBack {G : Type*} [Group G] (A B : G) (k : ℕ) : Prop :=
  (∃ σ, IsRun A B σ ∧ (backSteps A B σ).ncard = k) ∧
    ∀ σ, IsRun A B σ → k ≤ (backSteps A B σ).ncard

/-- The leapfrog's kick on one mode over `Z/n`: `K = K(1)`. -/
@[ledger "def:extent"]
abbrev leapK (n : ℕ) : SpecialLinearGroup (Fin 2) (ZMod n) := (Step.kick (1 : ZMod n)).sl

/-- The leapfrog's move on one mode over `Z/n`: `M = M(-1)`. -/
@[ledger "def:extent"]
abbrev leapM (n : ℕ) : SpecialLinearGroup (Fin 2) (ZMod n) := (Step.move (-1 : ZMod n)).sl

/-- `PSL(2, Z/n) = SL(2, Z/n)/{±1}`. -/
@[ledger "def:extent"]
abbrev PSLZ (n : ℕ) : Type := SpecialLinearGroup (Fin 2) (ZMod n) ⧸ pmOne n

/-- The kick in `PSL(2, Z/n)`. -/
@[ledger "def:extent"]
abbrev barK (n : ℕ) : PSLZ n := (leapK n : SpecialLinearGroup (Fin 2) (ZMod n))

/-- The move in `PSL(2, Z/n)`. -/
@[ledger "def:extent"]
abbrev barM (n : ℕ) : PSLZ n := (leapM n : SpecialLinearGroup (Fin 2) (ZMod n))

/-- The forward extents of `SL(2, Z/n)` under `K` and `M`. -/
@[ledger "def:extent"]
def extentsSL (n : ℕ) : Set (Perm (SpecialLinearGroup (Fin 2) (ZMod n))) :=
  {σ | IsExtent (leapK n) (leapM n) σ}

/-- The forward extents of `PSL(2, Z/n)` under `K` and `M`. -/
@[ledger "def:extent"]
def extentsPSL (n : ℕ) : Set (Perm (PSLZ n)) := {σ | IsExtent (barK n) (barM n) σ}

/-- The book's first square turned on the six corners of the two squares, numbered as `v₀, …, v₅`:
`L = (v₀ v₁ v₂ v₃)`. -/
@[ledger "def:two-squares"]
def squareL : Perm (Fin 6) := ⟨![1, 2, 3, 0, 4, 5], ![3, 0, 1, 2, 4, 5], by decide, by decide⟩

/-- The book's second square: `R = (v₁ v₄ v₅ v₂)`. -/
@[ledger "def:two-squares"]
def squareR : Perm (Fin 6) := ⟨![0, 4, 1, 3, 5, 2], ![0, 2, 5, 3, 1, 4], by decide, by decide⟩

/-- The group of the two squares. -/
@[ledger "def:two-squares"]
def twoSquares : Subgroup (Perm (Fin 6)) := Subgroup.closure {squareL, squareR}

/-- The turn `L` in the group of the two squares. -/
@[ledger "def:two-squares"]
def turnL : twoSquares := ⟨squareL, Subgroup.subset_closure (by simp)⟩

/-- The turn `R` in the group of the two squares. -/
@[ledger "def:two-squares"]
def turnR : twoSquares := ⟨squareR, Subgroup.subset_closure (by simp)⟩

/-- The field `F₅`. -/
@[ledger "def:two-squares"]
abbrev K5 := ZMod 5

/-- `5` is a prime. -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The six corners on the projective line over `F₅`: `v₀ ↦ ∞`, `v_k ↦ k - 1`. -/
@[ledger "def:two-squares"]
def pointOf : Fin 6 → Option K5 := ![none, some 0, some 1, some 2, some 3, some 4]

/-- The labelling of the corners is one to one and onto. -/
theorem pointOf_bijective : Function.Bijective pointOf := by decide

/-- The labelling of the corners as a bijection onto the projective line. -/
@[ledger "def:two-squares"]
noncomputable def corner : Fin 6 ≃ OnePoint K5 :=
  Equiv.ofBijective pointOf pointOf_bijective

/-- The action of `GL(2, F₅)` on the projective line, whose image is `PGL(2, 5)`. -/
@[ledger "def:two-squares"]
noncomputable def rho : Matrix.GeneralLinearGroup (Fin 2) K5 →* Perm (OnePoint K5) :=
  MulAction.toPermHom _ _

/-- The matrix of `L`, `x ↦ 1 / (2 x + 1)`. -/
@[ledger "def:two-squares"]
def matL : Matrix.GeneralLinearGroup (Fin 2) K5 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 2, 1] (by rw [Matrix.det_fin_two_of]; decide)

/-- The matrix of `R`, `x ↦ 2 x + 3`. -/
@[ledger "def:two-squares"]
def matR : Matrix.GeneralLinearGroup (Fin 2) K5 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![2, 3; 0, 1] (by rw [Matrix.det_fin_two_of]; decide)

/-- The matrix of the kick of strength `2`, `x ↦ x / (2 x + 1)`. -/
@[ledger "def:two-squares"]
def matK2 : Matrix.GeneralLinearGroup (Fin 2) K5 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 2, 1] (by rw [Matrix.det_fin_two_of]; decide)

/-- The permutations of the corners carried to the projective line by the labelling. -/
@[ledger "def:two-squares"]
noncomputable def toLine : Perm (Fin 6) ≃* Perm (OnePoint K5) := corner.permCongrHom

/-- A labelling of the corners makes the turns Möbius maps. -/
@[ledger "def:two-squares"]
def IsMobiusLabelling (c : Fin 6 ≃ OnePoint K5) : Prop :=
  c.permCongr squareL ∈ rho.range ∧ c.permCongr squareR ∈ rho.range

/-- The turn `L` on a state over `F₅`. -/
@[ledger "def:two-squares"]
def stateL (u : K5 × K5) : K5 × K5 := (u.2, 2 * u.1 + u.2)

/-- The turn `R` on a state over `F₅`. -/
@[ledger "def:two-squares"]
def stateR (u : K5 × K5) : K5 × K5 := (2 * u.1 + 3 * u.2, u.2)

/-- The determinant of two states over `F₅`. -/
@[ledger "def:two-squares"]
def detK5 (u v : K5 × K5) : K5 := u.1 * v.2 - u.2 * v.1

end Bells

/-! ## The step groups of one mode (the ledger's finding 037) -/

namespace StepGroup

/-- The kick `K = K(1)` over `ℤ`. -/
@[ledger "def:step-group"]
abbrev Kz : SpecialLinearGroup (Fin 2) ℤ := (Step.kick (1 : ℤ)).sl

/-- The move `M = M(-μ)` over `ℤ`, at the pull `μ`. -/
@[ledger "def:step-group"]
abbrev Mz (μ : ℤ) : SpecialLinearGroup (Fin 2) ℤ := (Step.move (-μ)).sl

/-- The step group `Σ_μ`: the laws of the one-mode scores at the pull `μ`. -/
@[ledger "def:step-group"]
def stepGroup (μ : ℤ) : Subgroup (SpecialLinearGroup (Fin 2) ℤ) :=
  Subgroup.closure {Kz, Mz μ}

/-- `Γ¹(μ)`: the laws `[[a, b], [c, d]]` with `b ≡ 0` and `a ≡ d ≡ 1` modulo `μ`. -/
@[ledger "def:step-group"]
def gammaUpper (μ : ℕ) : Subgroup (SpecialLinearGroup (Fin 2) ℤ) where
  carrier := {g | ((g.1 0 0 : ℤ) : ZMod μ) = 1 ∧ ((g.1 0 1 : ℤ) : ZMod μ) = 0 ∧
    ((g.1 1 1 : ℤ) : ZMod μ) = 1}
  mul_mem' := by
    rintro g h ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Int.cast_add, Int.cast_mul, h1, h2, h3, h4, h5, h6]
    simp
  one_mem' := by simp
  inv_mem' := by
    rintro g ⟨h1, h2, h3⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [h1, h2, h3]

/-- The growth per tick for `μ ≥ 5`: `ρ = (μ - 2 + √(μ² - 4μ))/2`. -/
@[ledger "def:step-group"]
noncomputable def growth (μ : ℝ) : ℝ := (μ - 2 + Real.sqrt (μ ^ 2 - 4 * μ)) / 2

end StepGroup

/-! ## The regular map of a dial (the ledger's finding 038, Theorem U) -/

namespace Klein

variable {n : ℕ}

/-- A state of one mode on the dial `Z/n`: the vector `(b, e)`. -/
@[ledger "def:klein-map"]
abbrev State (n : ℕ) := ZMod n × ZMod n

/-- The determinant of two states. -/
@[ledger "def:klein-map"]
def det2 (u v : State n) : ZMod n := u.1 * v.2 - u.2 * v.1

/-- A primitive state: its entries generate the unit ideal. -/
@[ledger "def:klein-map"]
def IsPrim (u : State n) : Prop := ∃ a b : ZMod n, a * u.1 + b * u.2 = 1

/-- States up to sign. -/
@[ledger "def:klein-map"]
def signSetoid (n : ℕ) : Setoid (State n) where
  r u v := u = v ∨ u = -v
  iseqv := ⟨fun _ => Or.inl rfl,
    fun h => h.elim (fun e => Or.inl e.symm) (fun e => Or.inr (by rw [e, neg_neg])),
    fun h1 h2 => by
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp⟩

/-- The class `[u]` of a state up to sign. -/
@[ledger "def:klein-map"]
abbrev Cls (n : ℕ) := Quotient (signSetoid n)

/-- The class of a state. -/
@[ledger "def:klein-map"]
def cls (u : State n) : Cls n := Quotient.mk _ u

/-- The vertices of the map: primitive states up to sign. -/
@[ledger "def:klein-map"]
def vertices (n : ℕ) : Set (Cls n) := {x | ∃ u : State n, IsPrim u ∧ cls u = x}

/-- The directed edges: `[u] → [v]` with `det(u, v) = 1`, for some representatives. -/
@[ledger "def:klein-map"]
def dirEdges (n : ℕ) : Set (Cls n × Cls n) :=
  {p | ∃ u v : State n, det2 u v = 1 ∧ cls u = p.1 ∧ cls v = p.2}

/-- The edges: the sets `{[u], [v]}` with `det(u, v) = 1`. -/
@[ledger "def:klein-map"]
def edges (n : ℕ) : Set (Set (Cls n)) :=
  {S | ∃ u v : State n, det2 u v = 1 ∧ S = {cls u, cls v}}

/-- The faces: the sets `{[u], [v], [u + v]}` with `det(u, v) = 1`. -/
@[ledger "def:klein-map"]
def faces (n : ℕ) : Set (Set (Cls n)) :=
  {S | ∃ u v : State n, det2 u v = 1 ∧ S = {cls u, cls v, cls (u + v)}}

/-- A law acting on a state. -/
@[ledger "def:klein-map"]
def act (g : SpecialLinearGroup (Fin 2) (ZMod n)) (u : State n) : State n :=
  (g.1 0 0 * u.1 + g.1 0 1 * u.2, g.1 1 0 * u.1 + g.1 1 1 * u.2)

/-- The all-flux state `B = (1, 0)`. -/
@[ledger "def:klein-map"]
def eB : State n := (1, 0)

/-- The all-electric state `E = (0, 1)`. -/
@[ledger "def:klein-map"]
def eE : State n := (0, 1)

/-- The directed edge of a law: the classes of its two columns, `[g B] → [g E]`. -/
@[ledger "def:klein-map"]
def toDir (g : SpecialLinearGroup (Fin 2) (ZMod n)) : Cls n × Cls n :=
  (cls (act g eB), cls (act g eE))

/-- The neighbours of a class: the targets of its directed edges. -/
@[ledger "def:klein-map"]
def neighbours (x : Cls n) : Set (Cls n) := {y | (x, y) ∈ dirEdges n}

/-- The tick at the pull `μ` on the dial `Z/n`. -/
@[ledger "def:klein-map"]
def tickN (μ : ZMod n) : SpecialLinearGroup (Fin 2) (ZMod n) := realize [.kick 1, .move (-μ)]

/-- `SL(2, Z/n)` acts on states up to sign. -/
@[ledger "def:klein-map"]
instance : MulAction (SpecialLinearGroup (Fin 2) (ZMod n)) (Cls n) where
  smul g := Quotient.map (act g) (by
    rintro u v (rfl | rfl)
    · exact Or.inl rfl
    · refine Or.inr ?_
      simp only [act, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, Prod.mk.injEq]
      constructor <;> ring)
  one_smul x := by
    induction x using Quotient.inductionOn with | _ u => ?_
    have : act (1 : SpecialLinearGroup (Fin 2) (ZMod n)) u = u := by simp [act]
    exact congrArg cls this
  mul_smul g h x := by
    induction x using Quotient.inductionOn with | _ u => ?_
    have : act (g * h) u = act g (act h u) := by
      simp only [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        Prod.mk.injEq]
      constructor <;> ring
    exact congrArg cls this

end Klein

/-! ## Steps on several channels (the ledger's R2) -/

/-- A step on `c` channels: `e_ij(f)` adds `f` times channel `j` to channel `i`. -/
@[ledger "def:step"]
structure ChanStep (c : ℕ) (S : Type*) where
  /-- The channel that changes. -/
  i : Fin c
  /-- The channel that is read. -/
  j : Fin c
  /-- The stencil. -/
  f : S

/-- The law of a step on `c` channels: `1 + f E_ij`, Mathlib's transvection. -/
@[ledger "def:step"]
def ChanStep.mat {c : ℕ} {S : Type*} [CommRing S] (s : ChanStep c S) : Matrix (Fin c) (Fin c) S :=
  Matrix.transvection s.i s.j s.f

/-- The realizer on `c` channels, in time order: the first letter acts first. -/
@[ledger "def:realizer"]
def realizeC {c : ℕ} {S : Type*} [CommRing S] : List (ChanStep c S) → Matrix (Fin c) (Fin c) S
  | [] => 1
  | s :: w => realizeC w * s.mat

/-- `E₂(S)`: the subgroup of `GL₂(S)` generated by the steps. -/
@[ledger "def:realizer"]
def elementary (S : Type*) [CommRing S] : Subgroup (Matrix.GeneralLinearGroup (Fin 2) S) :=
  Subgroup.closure (Set.range fun s : Step S =>
    ((s.sl : SpecialLinearGroup (Fin 2) S) : Matrix.GeneralLinearGroup (Fin 2) S))

/-! ## The face form and the link form (the ledger's T11) -/

section FaceLink

variable (R : Type*) [CommRing R]

/-- The difference `D = 1 - x`. -/
@[ledger "def:face-form"]
noncomputable def diffD : LaurentPolynomial R := 1 - LaurentPolynomial.T 1

/-- The dual difference `D* = 1 - 1/x`. -/
@[ledger "def:face-form"]
noncomputable def diffDs : LaurentPolynomial R := 1 - LaurentPolynomial.T (-1)

/-- The stencil `g = 2 - x - 1/x`. -/
@[ledger "def:face-form"]
noncomputable def stencilG : LaurentPolynomial R :=
  2 - LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)

/-- The change of variables `E = D* e`: `Λ = diag(1, D*)`. -/
@[ledger "def:face-form"]
noncomputable def lambdaMat : Matrix (Fin 2) (Fin 2) (LaurentPolynomial R) :=
  !![1, 0; 0, diffDs R]

/-- Evaluation at the zero mode `x = 1`. -/
@[ledger "def:face-form"]
noncomputable def atZero : LaurentPolynomial R →+* R :=
  LaurentPolynomial.eval₂ (RingHom.id R) 1

variable {R}

/-- The face form of a step with the weight `w`: `K(w κ)` and `M(-w ℓ g)`. -/
@[ledger "def:face-form"]
noncomputable def faceStep (κ ℓ : R) : Step R → Step (LaurentPolynomial R)
  | .kick w => .kick (LaurentPolynomial.C (w * κ))
  | .move w => .move (LaurentPolynomial.C (-(w * ℓ)) * stencilG R)

/-- The link form of the same step: `K(w κ D*)` and `M(-w ℓ D)`. -/
@[ledger "def:face-form"]
noncomputable def linkStep (κ ℓ : R) : Step R → Step (LaurentPolynomial R)
  | .kick w => .kick (LaurentPolynomial.C (w * κ) * diffDs R)
  | .move w => .move (LaurentPolynomial.C (-(w * ℓ)) * diffD R)

/-- The total kick of a score of weights. -/
@[ledger "def:face-form"]
def totalKick : List (Step R) → R
  | [] => 0
  | .kick w :: l => w + totalKick l
  | .move _ :: l => totalKick l

end FaceLink

/-! ## Callers and cues (the ledger's T14 and T16) -/

section Cue

/-- A caller's rule on the four equally prepared patterns of two response cells. -/
@[ledger "def:cut"]
abbrev Rule := Bool × Bool → Bool

/-- The share of the patterns that a rule sends to the first order. -/
@[ledger "def:cut"]
def share (r : Rule) : ℚ := ((Finset.univ.filter fun p => r p = true).card : ℚ) / 4

/-- The book's rule: turn on `11`. -/
@[ledger "def:cut"]
def turnOn11 : Rule := fun p => p.1 && p.2

/-- The rule: turn on `a = 1`. -/
@[ledger "def:cut"]
def turnOnA : Rule := fun p => p.1

/-- The rule: turn on `a ≠ b`. -/
@[ledger "def:cut"]
def turnOnNe : Rule := fun p => p.1 != p.2

open scoped Classical in
/-- Multiplication by the indicator of a set of cells. -/
@[ledger "def:cut"]
noncomputable def maskField {Λ R : Type*} [Zero R] (X : Set Λ) (u : Λ → R) : Λ → R :=
  fun z => if z ∈ X then u z else 0

/-- The shift of a field. -/
@[ledger "def:cut"]
def shiftField {Λ R : Type*} [Add Λ] (w : Λ) (u : Λ → R) : Λ → R := fun z => u (z + w)

end Cue

end Artform.Scores
