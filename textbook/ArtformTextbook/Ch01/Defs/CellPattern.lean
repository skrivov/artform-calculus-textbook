import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import ArtformTextbook.Meta.Book

/-!
# Finite cell patterns (*Constructing a space and its states*)

Definition 1.11: a finite cell pattern has typed cells with their grading, an
immediate-face relation that raises dimension by one, and a declared outer
boundary that is face-closed. Its local boundary data are the faces around
each cell. Orientation is an enrichment, and a palette assigns allowed values
to selected cells.

* `CellPattern`: the cells, graded by dimension (vertices `0`, edges `1`,
  faces `2`, and so on), the immediate-face relation `a ⋖ b`, and the outer
  boundary. Face-closure is stated for immediate faces; for iterated faces it
  follows (`CellPattern.mem_boundary_of_transGen`).
* `CellPattern.faces`: the local boundary data of a cell.
* `CellPattern.Orientation`: a source and a target for each edge, and a
  boundary word in oriented edges for each face.
* `CellPattern.Palette`: allowed labels or states for selected cells.

The canvases of Definition 3.1 are cell patterns without their outer boundary:
`IncidenceCanvas` keeps the incidence, and `Canvas` keeps a two-dimensional
orientation.
-/

namespace Artform

/-- **Definition 1.11** (finite cell pattern). Typed cells with their grading,
the dimension of each cell: vertices have dimension `0`, edges `1`, faces `2`,
and higher cells more. The immediate-face relation `a ⋖ b` raises dimension by
one. The declared outer boundary is face-closed: with any cell it contains
that cell's immediate faces, and so their faces, and so on. -/
@[book "def:finite-cell-pattern"]
structure CellPattern where
  /-- The cells. -/
  Cell : Type
  [fintype : Fintype Cell]
  [decEq : DecidableEq Cell]
  /-- The grading: the dimension of each cell. -/
  dim : Cell → ℕ
  /-- The immediate-face relation: `Face a b` is `a ⋖ b`. -/
  Face : Cell → Cell → Prop
  /-- An immediate face is one dimension lower. -/
  face_dim : ∀ a b, Face a b → dim b = dim a + 1
  /-- The declared outer boundary. -/
  boundary : Set Cell
  /-- The boundary is face-closed. -/
  boundary_closed : ∀ a b, Face a b → b ∈ boundary → a ∈ boundary

attribute [instance] CellPattern.fintype CellPattern.decEq

namespace CellPattern

variable (X : CellPattern)

/-- **Definition 1.11** (local boundary data): the faces around a cell. They
differ from the outer-boundary mark: an interior square has four sides,
although none of them need lie on the outer boundary. -/
@[book "def:finite-cell-pattern"]
def faces (b : X.Cell) : Set X.Cell := {a | X.Face a b}

/-- With any cell, the boundary contains its faces, their faces, and so on: an
edge in the boundary brings both endpoints with it. -/
theorem mem_boundary_of_transGen {a b : X.Cell} (h : Relation.TransGen X.Face a b)
    (hb : b ∈ X.boundary) : a ∈ X.boundary := by
  induction h with
  | single h => exact X.boundary_closed _ _ h hb
  | tail _ h ih => exact ih (X.boundary_closed _ _ h hb)

/-- The edges: the cells of dimension one. -/
abbrev Edge : Type := {e : X.Cell // X.dim e = 1}

/-- The faces in the sense of two-cells: the cells of dimension two. -/
abbrev TwoCell : Type := {f : X.Cell // X.dim f = 2}

/-- **Definition 1.11** (orientation), an enrichment. An oriented edge has a
source and a target, its two endpoints; an oriented face carries a boundary
word in oriented edges, each letter an edge of the face with `true` when the
word runs along the edge's direction. -/
@[book "def:finite-cell-pattern"]
structure Orientation where
  /-- The source of each edge. -/
  src : X.Edge → X.Cell
  /-- The target of each edge. -/
  tgt : X.Edge → X.Cell
  /-- The source is a face of the edge. -/
  src_face : ∀ e, X.Face (src e) e
  /-- The target is a face of the edge. -/
  tgt_face : ∀ e, X.Face (tgt e) e
  /-- Every face of an edge is its source or its target. -/
  face_src_or_tgt : ∀ (e : X.Edge) a, X.Face a e → a = src e ∨ a = tgt e
  /-- The boundary word of each face. -/
  word : X.TwoCell → List (X.Edge × Bool)
  /-- The letters of a face's word are edges of that face. -/
  word_face : ∀ f, ∀ p ∈ word f, X.Face p.1 f

/-- **Definition 1.11** (palette): the allowed labels or states of selected
cells, as the temporal palette of *Time, clocks, and measurement* lists the
allowed values of each row. -/
@[book "def:finite-cell-pattern"]
structure Palette where
  /-- The selected cells. -/
  selected : Set X.Cell
  /-- The labels or states allowed at each selected cell. -/
  Allowed : selected → Type

end CellPattern

/-! ## Non-vacuity -/

/-- One edge with its two endpoints, the whole pattern as outer boundary: cells
`0` and `1` are the vertices and cell `2` the edge. -/
abbrev segmentPattern : CellPattern where
  Cell := Fin 3
  dim c := if c = 2 then 1 else 0
  Face a b := b = 2 ∧ a ≠ 2
  face_dim a b h := by obtain ⟨rfl, h⟩ := h; simp [h]
  boundary := Set.univ
  boundary_closed _ _ _ _ := Set.mem_univ _

/-- The segment, oriented from `0` to `1`. -/
def segmentOrientation : segmentPattern.Orientation where
  src _ := 0
  tgt _ := 1
  src_face := by decide
  tgt_face := by decide
  face_src_or_tgt := by decide
  word _ := []
  word_face := by decide

end Artform
