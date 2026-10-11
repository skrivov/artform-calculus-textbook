import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Defs
import ArtformTextbook.Ch05.Defs.Calculus

/-!
# A square window, and a law of two steps on it (Section 6.9)

The canvas `SquareGrid(m, n)`: `m` columns and `n` rows of squares, with the
vertices `(i, j)` for `i ≤ m`, `j ≤ n`, the edges stored right or up, and each
face read anticlockwise from its lower edge. The chapter's window `W` is
`SquareGrid(3, 3)`.

Proposition 6.11 lets a law of two steps carry `A` and `E` on the links: a kick
that adds to `E` a value computed from `A` on the faces at each link, by the
same additive rule at every face, and a move that adds to `A` a value computed
from each link's new `E`, by the same additive rule at every link.
-/

namespace Artform

/-- The vertices of `SquareGrid(m, n)`: the points `(i, j)`, `i ≤ m`, `j ≤ n`. -/
abbrev GridVertex (m n : ℕ) : Type := Fin (m + 1) × Fin (n + 1)

/-- The edges of `SquareGrid(m, n)`: the horizontal edge `inl (i, j)` from
`(i, j)` right to `(i + 1, j)`, and the vertical edge `inr (i, j)` from
`(i, j)` up to `(i, j + 1)`. -/
abbrev GridEdge (m n : ℕ) : Type := (Fin m × Fin (n + 1)) ⊕ (Fin (m + 1) × Fin n)

/-- The faces of `SquareGrid(m, n)`: the square `(i, j)` with lower left corner
`(i, j)`. -/
abbrev GridFace (m n : ℕ) : Type := Fin m × Fin n

/-- The source of an edge of `SquareGrid(m, n)`: its left or lower end. -/
def gridSrc {m n : ℕ} : GridEdge m n → GridVertex m n
  | .inl (i, j) => (i.castSucc, j)
  | .inr (i, j) => (i, j.castSucc)

/-- The target of an edge of `SquareGrid(m, n)`: its right or upper end. -/
def gridTgt {m n : ℕ} : GridEdge m n → GridVertex m n
  | .inl (i, j) => (i.succ, j)
  | .inr (i, j) => (i, j.succ)

/-- The four edges of the face `(i, j)`, read anticlockwise from its lower
edge: lower, right, upper, left. -/
def gridFaceEdge {m n : ℕ} (f : GridFace m n) : Fin 4 → GridEdge m n :=
  ![.inl (f.1, f.2.castSucc), .inr (f.1.succ, f.2), .inl (f.1, f.2.succ),
    .inr (f.1.castSucc, f.2)]

/-- Whether the boundary of a face, read anticlockwise, runs along each of its
four edges: along the lower and the right edge, against the upper and the
left one. -/
def gridFaceDir : Fin 4 → Bool := ![true, true, false, false]

/-- The canvas `SquareGrid(m, n)`, its edges stored right or up and each face
read anticlockwise from its lower edge. -/
abbrev squareGrid (m n : ℕ) : Canvas where
  V := GridVertex m n
  E := GridEdge m n
  F := GridFace m n
  src := gridSrc
  tgt := gridTgt
  boundary f := (List.finRange 4).map fun k => (gridFaceEdge f k, gridFaceDir k)
  closed f := by
    refine ⟨by simp [List.finRange_succ], ?_⟩
    simp [List.finRange_succ, gridFaceEdge, gridFaceDir, stepStart, stepEnd, gridSrc,
      gridTgt]

/-- The kick of Proposition 6.11, built face by face with one rule `r` for
every face: each face `f` reads the potential on its four edges, in the order
of `gridFaceEdge`, and adds `r` of what it reads at each of its four edges.
At an edge, the kick adds what the faces at it add there. -/
def faceKick {m n : ℕ} (r : (Fin 4 → ZMod 8) → Fin 4 → ZMod 8)
    (A : GridEdge m n → ZMod 8) : GridEdge m n → ZMod 8 := fun e =>
  ∑ f : GridFace m n, ∑ k : Fin 4,
    if gridFaceEdge f k = e then r (fun j => A (gridFaceEdge f j)) k else 0

/-- The tick of the two steps of Proposition 6.11, on a pair `(A, E)` of link
tables: the kick `E' = E + φ(A)`, with `φ` built face by face from the rule
`r`, then the move `A' = A + μ(E')`, the same rule `μ` at every link. -/
def twoStepTick {m n : ℕ} (r : (Fin 4 → ZMod 8) → Fin 4 → ZMod 8) (μ : ZMod 8 → ZMod 8)
    (s : (GridEdge m n → ZMod 8) × (GridEdge m n → ZMod 8)) :
    (GridEdge m n → ZMod 8) × (GridEdge m n → ZMod 8) :=
  let E' := s.2 + faceKick r s.1
  (fun e => s.1 e + μ (E' e), E')

end Artform
