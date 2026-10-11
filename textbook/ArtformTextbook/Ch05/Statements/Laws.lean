import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ArtformTextbook.Ch05.Defs.Current
import ArtformTextbook.Ch05.Defs.Realizers

/-!
# Statements of Chapter 5: tallies, laws and realizers

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

open scoped BigOperators

/-- **Proposition 5.8** (the current of a tally). Let an affine law
`F(p) = M(p) + b` keep the tally `T(p) = Σ_v d(v) p(v)`. For cells `u ≠ v` put
`J_{u→v}(p) = d(v) M_{vu} p(u)`. Then at every tick and every cell `v`
`d(v)(F(p)(v) − p(v)) = Σ_{u≠v} J_{u→v}(p) − Σ_{y≠v} J_{v→y}(p) + d(v) b(v)`,
and the source terms `d(v) b(v)` add up to `0`. The current runs from `u` to
`v` only if the update of `v` reads `u`, and it reads the cell `u` alone. -/
@[book "prop:tally-current"]
def tallyCurrent : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C] (n : ℕ) (L : AffineLaw C n) (d : C → ZMod n),
    L.toDetLaw.Conserved (fun p => ∑ v, d v * p v) →
      (∀ (p : C → ZMod n) (v : C), d v * (L.tick p v - p v) =
          ∑ u ∈ Finset.univ.erase v, L.current d u v p -
          ∑ y ∈ Finset.univ.erase v, L.current d v y p + d v * L.b v) ∧
      ∑ v, d v * L.b v = 0 ∧
      (∀ (u v : C) (p : C → ZMod n), L.current d u v p ≠ 0 → L.coeff v u ≠ 0) ∧
      (∀ (u v : C) (p q : C → ZMod n), p u = q u → L.current d u v p = L.current d u v q)

/-- **Proposition 5.11** (the law decides what is kept). If every batch a law
allows carries states satisfying an invariant to states satisfying it, then
every run keeps the invariant: the run of a deterministic realizer, each run a
relational realizer allows, and each run of positive weight under a
stochastic one. -/
@[book "prop:law-decides"]
def lawDecides : Prop :=
  ∀ (A : Presentation) (L : Law A) (J : A.Table → Prop),
    (∀ (x : A.Table), L.Legal x → ∀ b : Batch A x, L.Allows b → J x → J b.apply) →
    (∀ (R : DetRealizer L) (n : ℕ) (r : Run A n), r.OfDet R →
      J (r.state 0) → ∀ i, J (r.state i)) ∧
    (∀ (R : RelRealizer L) (n : ℕ) (r : Run A n), r.OfRel R →
      J (r.state 0) → ∀ i, J (r.state i)) ∧
    (∀ (R : StochRealizer L) (n : ℕ) (r : Run A n), r.OfStoch R →
      J (r.state 0) → ∀ i, J (r.state i))

end Artform.Statement
