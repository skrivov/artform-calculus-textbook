import ArtformTextbook.Ch03.Defs.Views
import ArtformTextbook.Ch06.Defs.Window
import ArtformTextbook.Ch12.Groups

/-!
# One square, three encodings

The book's square is written three times in this library: as the cubical
descriptor `{0, 1, *}²` of Chapter 3 (`squareCanvas`), as `SquareGrid(1, 1)` of
Chapter 6 (`squareGrid 1 1`), and as the cycle of four edges of Chapter 12
(`ColourGroups.squareCanvas`). The three are instances of one geometric form
(Definition 1.12), the descriptor, by structural isomorphisms that keep the
dimension and the immediate incidence of every cell.
-/

namespace Artform

namespace SquareForms

/-- The two values of a coordinate. -/
def bit : Fin 2 → Tri := ![.zero, .one]

/-- The address of each cell of the square of Chapter 12: the vertices
`0, 1, 2, 3` anticlockwise from the lower left corner, the edge `i → i + 1`,
and the face. -/
def cycleAddress : Fin 4 ⊕ Fin 4 ⊕ Unit → (Fin 2 → Tri)
  | .inl v => ![![.zero, .zero], ![.one, .zero], ![.one, .one], ![.zero, .one]] v
  | .inr (.inl e) => ![![.star, .zero], ![.one, .star], ![.star, .one], ![.zero, .star]] e
  | .inr (.inr _) => ![.star, .star]

/-- The address of each cell of `SquareGrid(1, 1)`: the vertex `(i, j)`, the
horizontal edge at height `j`, the vertical edge at abscissa `i`, and the
face. -/
def gridAddress : (Fin 2 × Fin 2) ⊕ ((Fin 1 × Fin 2) ⊕ (Fin 2 × Fin 1)) ⊕ (Fin 1 × Fin 1) →
    (Fin 2 → Tri)
  | .inl (i, j) => ![bit i, bit j]
  | .inr (.inl (.inl (_, j))) => ![.star, bit j]
  | .inr (.inl (.inr (i, _))) => ![bit i, .star]
  | .inr (.inr _) => ![.star, .star]

theorem cycleAddress_bijective : Function.Bijective cycleAddress := by decide

theorem gridAddress_bijective : Function.Bijective gridAddress := by decide

/-- The square of Chapter 12, read as the descriptor. -/
noncomputable def cycleIso : ColourGroups.squareCanvas.toIncidenceCanvas.Iso squareCanvas where
  toEquiv := Equiv.ofBijective cycleAddress cycleAddress_bijective
  dim_eq := by decide
  face_iff := by decide

/-- `SquareGrid(1, 1)`, read as the descriptor. -/
noncomputable def gridIso : (squareGrid 1 1).toIncidenceCanvas.Iso squareCanvas where
  toEquiv := Equiv.ofBijective gridAddress gridAddress_bijective
  dim_eq := by decide
  face_iff := by decide

/-- The three squares are instances of one geometric form, the descriptor
`{0, 1, *}²` (Definition 1.12). -/
theorem one_form :
    ColourGroups.squareCanvas.toIncidenceCanvas.IsInstance squareCanvas ∧
      (squareGrid 1 1).toIncidenceCanvas.IsInstance squareCanvas ∧
      squareCanvas.IsInstance squareCanvas :=
  ⟨⟨cycleIso⟩, ⟨gridIso⟩, ⟨IncidenceCanvas.Iso.refl _⟩⟩

end SquareForms

end Artform
