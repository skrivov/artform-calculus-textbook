import Mathlib.Data.Set.Image
import Mathlib.Logic.Function.Iterate
import ArtformTextbook.Meta.Book

/-!
# Deterministic laws, symmetries and conserved readings (Sections 5.1 and 5.2)

The states of a frame are a type `S` here; Definition 1.13 builds them from
the frame's positions and values.
-/

namespace Artform

-- ANCHOR: ldetlaw
/-- **Definition 5.1** (deterministic law; tick; run). A deterministic law on
a frame gives each state the state that follows it; the map that does so is
the law's tick. -/
@[book "def:tick"]
structure DetLaw (S : Type*) where
  /-- The tick: the state that follows each state. -/
  tick : S → S

namespace DetLaw

variable {S : Type*} (L : DetLaw S)

/-- The run of the law from `x`: `x, F(x), F(F(x)), …`, one state at every
tick. -/
def run (x : S) (n : ℕ) : S := L.tick^[n] x

/-- **Definition 5.3** (symmetry of a law). A symmetry is a script `s` on the
states that commutes with the tick: `F(s(x)) = s(F(x))` for every state `x`. -/
@[book "def:law-symmetry"]
def IsSymmetry (s : S → S) : Prop := ∀ x, L.tick (s x) = s (L.tick x)

/-- **Definition 5.3** (conserved reading). A reading `q` is conserved when
`q(F(x)) = q(x)` for every state `x`. -/
@[book "def:law-symmetry"]
def Conserved {V : Type*} (q : S → V) : Prop := ∀ x, q (L.tick x) = q x
-- ANCHOR_END: ldetlaw

/-- The orbit of a state: `{x, F(x), F²(x), …}` (Section 5.2). -/
def orbit (x : S) : Set S := Set.range (L.run x)

end DetLaw

end Artform
