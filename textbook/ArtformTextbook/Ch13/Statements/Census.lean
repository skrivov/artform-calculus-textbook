import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.ConjFinite
import ArtformTextbook.Ch12.Defs.ColourGroups
import ArtformTextbook.Ch13.Defs.Census

/-!
# Statements of Chapter 13: the census of a canvas

Each statement of the book is a proposition here, tagged with the book's label. Its proof,
elsewhere in the chapter's folder, is a theorem whose type is exactly this proposition.

The setting is that of `Ch13/Defs/Census.lean`: a canvas `K`, a finite group `G` with a triplet
`ρ : G →* Matrix C C ℂ` (the book's colour groups are subgroups of `SU(3)`, with `C = Fin 3` and
`ρ` the inclusion), `d = |S|` slots at every vertex, and the modes of the canvas in any order.
-/

namespace Artform.Statement

open scoped Matrix

open Polynomial Classical in
/-- **Theorem 13.11** (census of a canvas). On a connected canvas with `V` vertices, `E` edges and
`d` slots at every vertex, the number of colourless states with `n` quarks is the coefficient of
`z^n` in `Σ_C |C_G(C)|^{E-V} det(1 + z g_C)^{dV}`, the sum over the conjugacy classes `C` of `G`,
with `g_C` an element of `C` and `C_G(C)` its centralizer. Without matter the count is
`Σ_C |C_G(C)|^{E-V}`: one state on a tree, one per class on a canvas with a single loop, and
`336 465` for the cube group on the cube. The zero-flux states number the one-vertex count to the
power `V`.

The colour group is any finite group `G` with any triplet `ρ : G →* Matrix C C ℂ` (the book: a
finite subgroup of `SU(3)` and its inclusion, so that `det(1 + z g)` is `det(1 + z ρ(g))`), and the
modes of the canvas are in any order `ord`. A canvas is connected when its transport skeleton is
(`Skeleton.Connected`) and it has a vertex. "The number of colourless states with `n` quarks" is
the dimension of the colourless states whose every coefficient table has `n` quarks; `V` and `E`
are the numbers of vertices and edges, and `|C_G(C)|^{E-V}` is an integer power, `E - V` being
`-1` on a tree. The elements `g_C` are any choice of an element in each class. "Without matter"
is the canvas with no slots, whose colourless states are the gauge-invariant tables over the link
tables (`Canvas.gaugeInvariants`). A tree is a connected canvas with `E = V - 1`, and a canvas
with a single loop a connected canvas with `E = V`. The cube is the boundary of the cube with
its `8` vertices, `12` edges and `6` faces (`Canvas.cube`), and the cube group its group of
rotations (`cubeGroup`). "The one-vertex count" is the number of invariant occupation tables of
one vertex with `d` slots (`Edge.vertexInvariants`, in any order of its modes); the zero-flux
count holds on every canvas, connected or not. -/
@[book "thm:ml-canvas-census"]
def mlCanvasCensus : Prop :=
  (∀ (G : Type) [Group G] [Fintype G] (C S : Type) [Fintype C] [DecidableEq C] [Fintype S]
      [DecidableEq S] (ρ : G →* Matrix C C ℂ) (K : Canvas), Nonempty K.V →
      K.skeleton.Connected → ∀ (ord : LinearOrder (K.Mode C S)) (g : ConjClasses G → G),
      (∀ c, ConjClasses.mk (g c) = c) → ∀ n : ℕ,
      (Module.finrank ℂ ↥(K.colourless ρ ord ⊓
          Edge.stateSector (K.skeleton.LinkTable G) (Fock.numberSector (K.Mode C S) n)) : ℂ) =
        (∑ c : ConjClasses G, ((Nat.card (Subgroup.centralizer {g c}) : ℂ) ^
            ((Fintype.card K.E : ℤ) - Fintype.card K.V)) •
          (1 + (X : ℂ[X]) • (ρ (g c)).map Polynomial.C).det ^
            (Fintype.card S * Fintype.card K.V)).coeff n) ∧
  (∀ (G : Type) [Group G] [Fintype G] (K : Canvas), Nonempty K.V → K.skeleton.Connected →
      ∀ g : ConjClasses G → G, (∀ c, ConjClasses.mk (g c) = c) →
      (Module.finrank ℂ ↥(K.gaugeInvariants G) : ℂ) =
        ∑ c : ConjClasses G, (Nat.card (Subgroup.centralizer {g c}) : ℂ) ^
          ((Fintype.card K.E : ℤ) - Fintype.card K.V)) ∧
  (∀ (G : Type) [Group G] [Fintype G] (K : Canvas), Nonempty K.V → K.skeleton.Connected →
      Fintype.card K.E + 1 = Fintype.card K.V →
      Module.finrank ℂ ↥(K.gaugeInvariants G) = 1) ∧
  (∀ (G : Type) [Group G] [Fintype G] (K : Canvas), Nonempty K.V → K.skeleton.Connected →
      Fintype.card K.E = Fintype.card K.V →
      Module.finrank ℂ ↥(K.gaugeInvariants G) = Nat.card (ConjClasses G)) ∧
  Module.finrank ℂ ↥(Canvas.cube.gaugeInvariants cubeGroup) = 336465 ∧
  (∀ (G : Type) [Group G] [Fintype G] (C S : Type) [Fintype C] [DecidableEq C] [Fintype S]
      [DecidableEq S] (ρ : G →* Matrix C C ℂ) (K : Canvas) (ord : LinearOrder (K.Mode C S))
      (ordv : LinearOrder (C × S)),
      Module.finrank ℂ ↥(K.zeroFlux ρ ord) =
        Module.finrank ℂ ↥(Edge.vertexInvariants ρ ordv) ^ Fintype.card K.V)

end Artform.Statement
