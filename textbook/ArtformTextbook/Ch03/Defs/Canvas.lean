import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Chain
import ArtformTextbook.Meta.Book

/-!
# The canvas (Section 3.1)

Definition 3.1 in dimension two, with its stored orientation, which is how
Chapters 5 and 6 use canvases: vertices, edges each stored with a direction,
and faces each with a closed boundary cycle read anticlockwise.
-/

namespace Artform

/-- Where a step of a boundary walk starts: a step `(e, true)` runs along the
stored direction of `e`, from its source to its target; `(e, false)` runs
against it. -/
def stepStart {V E : Type*} (src tgt : E → V) : E × Bool → V
  | (e, true) => src e
  | (e, false) => tgt e

/-- Where a step of a boundary walk ends. -/
def stepEnd {V E : Type*} (src tgt : E → V) : E × Bool → V
  | (e, true) => tgt e
  | (e, false) => src e

/-- A closed walk: a nonempty list of steps, each ending where the next one
starts, the last ending where the first starts. -/
def IsClosedWalk {V E : Type*} (src tgt : E → V) (w : List (E × Bool)) : Prop :=
  w ≠ [] ∧ List.IsChain (fun a b => stepEnd src tgt a = stepStart src tgt b) (w ++ w.take 1)

/-- **Definition 3.1** (finite cellular canvas), in dimension two, with its
stored orientation. The cells are the vertices `C₀`, the edges `C₁` and the
faces `C₂`. An edge is stored with a direction, from its source to its target,
which gives its two immediate faces among the vertices. A face carries a
closed boundary cycle, read anticlockwise: its edges in order, each with
`true` when the cycle runs along the edge's stored direction. The outer
boundary `∂X` of the definition is not part of this structure; no statement
of Chapters 5 and 6 uses it. -/
@[book "def:canvas"]
structure Canvas where
  /-- The vertices `C₀`. -/
  V : Type
  /-- The edges `C₁`. -/
  E : Type
  /-- The faces `C₂`. -/
  F : Type
  [fintypeV : Fintype V]
  [fintypeE : Fintype E]
  [fintypeF : Fintype F]
  [decEqV : DecidableEq V]
  [decEqE : DecidableEq E]
  [decEqF : DecidableEq F]
  /-- The source of each edge's stored direction. -/
  src : E → V
  /-- The target of each edge's stored direction. -/
  tgt : E → V
  /-- The boundary cycle of each face, read anticlockwise. -/
  boundary : F → List (E × Bool)
  /-- Every boundary cycle is closed. -/
  closed : ∀ f, IsClosedWalk src tgt (boundary f)

attribute [instance] Canvas.fintypeV Canvas.fintypeE Canvas.fintypeF
  Canvas.decEqV Canvas.decEqE Canvas.decEqF

namespace Canvas

variable (K : Canvas)

/-- How the boundary of face `f` reads edge `e`: the number of times it runs
along `e`, less the number of times it runs against it. This is the entry
`(D₁)_{e,f}` of the book's face-to-edge incidence matrix. -/
def inc (e : K.E) (f : K.F) : ℤ :=
  ((K.boundary f).map fun st => if st.1 = e then (if st.2 then 1 else -1) else 0).sum

/-- Each face read anticlockwise, as on a canvas drawn in the plane: no face
crosses an edge twice, and two different faces that share an edge read it in
opposite directions. -/
structure Anticlockwise : Prop where
  nodup : ∀ f, ((K.boundary f).map Prod.fst).Nodup
  opposite : ∀ e f g b c, f ≠ g → (e, b) ∈ K.boundary f → (e, c) ∈ K.boundary g → b ≠ c

end Canvas

end Artform
