import Mathlib.Algebra.Group.Basic
import ArtformTextbook.Meta.Book

/-!
# Right torsors (Section 5.8, Definition 5.15)

A right `G`-torsor is a set shaped like `G` with no element playing the part of
`1`: a right action of `G` that is free and transitive.
-/

namespace Artform

/-- **Definition 5.15** (right torsor), as a property of a set `T` with a map
`(x, g) ↦ x · g`. The map is a right action (`x · 1 = x` and
`(x · g) · k = x · (g k)`) on a nonempty set, and it is
1. free: `x · g = x` forces `g = 1`; and
2. transitive: for all `x, y ∈ T` there is `g` with `x · g = y`.

The book takes `G` finite and `T` a finite set. Lean asks for neither; for a
finite group nothing changes, since `g ↦ x · g` is then a bijection from `G`
onto `T`, which is therefore finite. -/
@[book "def:torsor"]
structure IsRightTorsor (G : Type*) [Group G] (T : Type*) (act : T → G → T) : Prop where
  /-- `x · 1 = x`. -/
  act_one : ∀ x, act x 1 = x
  /-- `(x · g) · k = x · (g k)`. -/
  act_mul : ∀ x g k, act (act x g) k = act x (g * k)
  /-- The set is nonempty. -/
  nonempty : Nonempty T
  /-- Free: `x · g = x` forces `g = 1`. -/
  free : ∀ x g, act x g = x → g = 1
  /-- Transitive: for all `x, y` there is `g` with `x · g = y`. -/
  transitive : ∀ x y, ∃ g, act x g = y

/-- **Definition 5.15** (right torsor): the type `Torsor(G)` of right
`G`-torsors, each a set `T` with a right action `(x, g) ↦ x · g` of `G` that is
free and transitive (`IsRightTorsor`). -/
@[book "def:torsor"]
structure RightTorsor (G : Type*) [Group G] where
  /-- The underlying set `T`. -/
  carrier : Type
  /-- The right action `(x, g) ↦ x · g`. -/
  act : carrier → G → carrier
  /-- The action is a right action, free and transitive, on a nonempty set. -/
  isRightTorsor : IsRightTorsor G carrier act

instance {G : Type*} [Group G] : CoeSort (RightTorsor G) Type := ⟨RightTorsor.carrier⟩

end Artform
