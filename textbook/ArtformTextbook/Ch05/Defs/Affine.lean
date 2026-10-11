import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring
import ArtformTextbook.Ch05.Defs.Laws

/-!
# Affine laws, tallies and pairings (Section 5.3), and the law of the square

The states are the tables on a finite set of cells `C` with values in
`ZMod n`, added cell by cell.
-/

namespace Artform

open scoped BigOperators

-- ANCHOR: laffine
/-- **Definition 5.5** (affine law). The tick has the form `F(p) = M(p) + b`,
where `M` is a bijection of the tables with `M(p + q) = M(p) + M(q)` and `b` is
a fixed table, the source. -/
@[book "def:affine-law"]
structure AffineLaw (C : Type*) (n : ℕ) where
  /-- The additive bijection `M`. -/
  M : (C → ZMod n) ≃+ (C → ZMod n)
  /-- The source `b`. -/
  b : C → ZMod n

namespace AffineLaw

variable {C : Type*} {n : ℕ}

/-- The tick `F(p) = M(p) + b`. -/
def tick (L : AffineLaw C n) (p : C → ZMod n) : C → ZMod n := L.M p + L.b

/-- The affine law as a deterministic law on the tables. -/
def toDetLaw (L : AffineLaw C n) : DetLaw (C → ZMod n) := ⟨L.tick⟩
-- ANCHOR_END: laffine

end AffineLaw

-- ANCHOR: ltally
/-- **Definition 5.5** (tally). A tally is an additive reading of the tables:
`T(p + q) = T(p) + T(q)`, with values in `ZMod n`. -/
@[book "def:affine-law"]
abbrev Tally (C : Type*) (n : ℕ) := (C → ZMod n) →+ ZMod n

/-- **Definition 5.5** (pairing). A pairing `⟨p, q⟩` is a tally in each
argument. -/
@[book "def:affine-law"]
abbrev Pairing (C : Type*) (n : ℕ) :=
  (C → ZMod n) →+ (C → ZMod n) →+ ZMod n

/-- **Definition 5.5** (perfect pairing): every tally is `⟨w, ·⟩` for exactly
one table `w`. -/
@[book "def:affine-law"]
def Pairing.Perfect {C : Type*} {n : ℕ} (P : Pairing C n) : Prop :=
  ∀ T : Tally C n, ∃! w, P w = T

/-- **Definition 5.5** (keeping a pairing): `⟨M(p), M(q)⟩ = ⟨p, q⟩` for all
tables `p`, `q`. -/
@[book "def:affine-law"]
def AffineLaw.Keeps {C : Type*} {n : ℕ} (L : AffineLaw C n)
    (P : Pairing C n) : Prop :=
  ∀ p q, P (L.M p) (L.M q) = P p q
-- ANCHOR_END: ltally

/-- The multiply-and-add pairing `⟨p, q⟩ = Σᵢ p(i) q(i)` of Section 5.3. -/
def dotPairing (C : Type*) [Fintype C] (n : ℕ) : Pairing C n :=
  AddMonoidHom.mk' (fun p => AddMonoidHom.mk' (fun q => ∑ i, p i * q i)
      (fun q q' => by simp [mul_add, Finset.sum_add_distrib]))
    (fun p p' => by ext q; simp [add_mul, Finset.sum_add_distrib])

/-! ## The law of the square (Section 5.1)

Its corners `v₀, …, v₃` are numbered anticlockwise, each holds a number modulo
`3`, and at every tick every number moves one corner on: `p'(vᵢ) = p(vᵢ₋₁)`. -/

-- ANCHOR: lsquare
/-- Moving every number one corner on: `p'(vᵢ) = p(vᵢ₋₁)`, indices modulo `4`. -/
def squareShift : (Fin 4 → ZMod 3) ≃+ (Fin 4 → ZMod 3) where
  toFun p i := p (i - 1)
  invFun p i := p (i + 1)
  left_inv p := by ext i; simp
  right_inv p := by ext i; simp
  map_add' p q := rfl

/-- The law of the square: the shift, with source `0`. -/
def squareLaw : AffineLaw (Fin 4) 3 := ⟨squareShift, 0⟩

/-- The total of the four numbers, `T(p) = p(v₀) + p(v₁) + p(v₂) + p(v₃)`
modulo `3`. -/
def squareTotal : Tally (Fin 4) 3 :=
  AddMonoidHom.mk' (fun p => p 0 + p 1 + p 2 + p 3)
    (fun p q => by simp only [Pi.add_apply]; ring)
-- ANCHOR_END: lsquare

end Artform
