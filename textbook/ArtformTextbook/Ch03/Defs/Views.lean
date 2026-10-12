import ArtformTextbook.Ch01.Defs.CellPattern
import ArtformTextbook.Ch03.Defs.Cube

/-!
# Canvases as cell patterns

The two Lean forms of Definition 3.1 are views of the finite cell patterns of
Definition 1.11.

* `CellPattern.toIncidenceCanvas`: a cell pattern with its outer boundary
  forgotten is an incidence canvas, which does not keep the boundary; and an
  incidence canvas with a face-closed boundary is a cell pattern
  (`IncidenceCanvas.toCellPattern`). The two maps are inverse on the
  incidence (`toCellPattern_toIncidenceCanvas`).
* `Canvas.orientation`: a two-dimensional canvas is an oriented cell pattern.
  Its incidence canvas (`Canvas.toIncidenceCanvas`) with an empty outer
  boundary carries the orientation of Definition 1.11: the stored direction
  of each edge, and the boundary cycle of each face as its boundary word.
-/

namespace Artform

/-- A cell pattern with its outer boundary forgotten: an incidence canvas. -/
def CellPattern.toIncidenceCanvas (X : CellPattern) : IncidenceCanvas where
  Cell := X.Cell
  dim := X.dim
  Face := X.Face
  face_dim := X.face_dim

/-- An incidence canvas with a declared outer boundary, face-closed: a cell
pattern. -/
def IncidenceCanvas.toCellPattern (X : IncidenceCanvas) (bd : Set X.Cell)
    (h : ∀ a b, X.Face a b → b ∈ bd → a ∈ bd) : CellPattern where
  Cell := X.Cell
  dim := X.dim
  Face := X.Face
  face_dim := X.face_dim
  boundary := bd
  boundary_closed := h

theorem IncidenceCanvas.toCellPattern_toIncidenceCanvas (X : IncidenceCanvas) (bd : Set X.Cell)
    (h : ∀ a b, X.Face a b → b ∈ bd → a ∈ bd) : (X.toCellPattern bd h).toIncidenceCanvas = X :=
  rfl

/-- The empty outer boundary is face-closed. -/
theorem IncidenceCanvas.empty_closed (X : IncidenceCanvas) :
    ∀ a b, X.Face a b → b ∈ (∅ : Set X.Cell) → a ∈ (∅ : Set X.Cell) :=
  fun _ _ _ h => h.elim

namespace Canvas

variable (K : Canvas)

/-- Whether a cell is an immediate face of another, in the incidence canvas of
a two-dimensional canvas, is decidable. -/
instance decidableFace : DecidableRel K.toIncidenceCanvas.Face := fun a b => by
  rcases a with v | e | f <;> rcases b with v' | e' | f' <;>
    simp only [Canvas.toIncidenceCanvas] <;> infer_instance

/-- A two-dimensional canvas as a cell pattern, with an empty outer boundary. -/
def toCellPattern : CellPattern :=
  K.toIncidenceCanvas.toCellPattern ∅ K.toIncidenceCanvas.empty_closed

@[simp] theorem dim_vertex (v : K.V) : K.toCellPattern.dim (.inl v) = 0 := rfl

@[simp] theorem dim_edge (e : K.E) : K.toCellPattern.dim (.inr (.inl e)) = 1 := rfl

@[simp] theorem dim_face (f : K.F) : K.toCellPattern.dim (.inr (.inr f)) = 2 := rfl

/-- The edge of the canvas that a one-cell of its cell pattern is. -/
def edgeOf : (c : K.V ⊕ K.E ⊕ K.F) → K.toCellPattern.dim c = 1 → K.E
  | .inr (.inl e), _ => e
  | .inl _, h => absurd h (by simp)
  | .inr (.inr _), h => absurd h (by simp)

/-- The face of the canvas that a two-cell of its cell pattern is. -/
def faceOf : (c : K.V ⊕ K.E ⊕ K.F) → K.toCellPattern.dim c = 2 → K.F
  | .inr (.inr f), _ => f
  | .inl _, h => absurd h (by simp)
  | .inr (.inl _), h => absurd h (by simp)

/-- The orientation of a two-dimensional canvas, as an orientation of its cell
pattern (Definition 1.11): each edge runs from its stored source to its stored
target, and each face carries its boundary cycle as its boundary word. -/
def orientation : K.toCellPattern.Orientation where
  src e := .inl (K.src (K.edgeOf e.1 e.2))
  tgt e := .inl (K.tgt (K.edgeOf e.1 e.2))
  src_face e := by
    obtain ⟨c, h⟩ := e
    rcases c with v | e | f
    · exact absurd h (by simp)
    · exact Or.inl rfl
    · exact absurd h (by simp)
  tgt_face e := by
    obtain ⟨c, h⟩ := e
    rcases c with v | e | f
    · exact absurd h (by simp)
    · exact Or.inr rfl
    · exact absurd h (by simp)
  face_src_or_tgt e a ha := by
    obtain ⟨c, h⟩ := e
    rcases c with v | e | f
    · exact absurd h (by simp)
    · rcases a with w | e' | f'
      · rcases ha with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact ha.elim
      · exact ha.elim
    · exact absurd h (by simp)
  word f := (K.boundary (K.faceOf f.1 f.2)).map fun p => (⟨.inr (.inl p.1), rfl⟩, p.2)
  word_face f p hp := by
    obtain ⟨c, h⟩ := f
    rcases c with v | e | f
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · simp only [List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact List.mem_map_of_mem hq

end Canvas

end Artform
