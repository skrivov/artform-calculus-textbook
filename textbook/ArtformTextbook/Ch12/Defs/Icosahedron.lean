import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Set.Card
import ArtformTextbook.Meta.Book

/-!
# The icosahedron (Section 12.3, Model II)

The twelve points `(0, ±1, ±φ)` and their two cyclic permutations
`(±φ, 0, ±1)` and `(±1, ±φ, 0)`, with `φ = (1 + √5)/2`, are the vertices of an
icosahedron; its rotations are the rotations of space that carry the twelve
to themselves.
-/

namespace Artform

open Real

/-- The twelve vertices of the icosahedron. -/
noncomputable def icoVertices : Set (Fin 3 → ℝ) :=
  {![0, 1, goldenRatio], ![0, 1, -goldenRatio], ![0, -1, goldenRatio], ![0, -1, -goldenRatio],
   ![goldenRatio, 0, 1], ![goldenRatio, 0, -1], ![-goldenRatio, 0, 1], ![-goldenRatio, 0, -1],
   ![1, goldenRatio, 0], ![1, -goldenRatio, 0], ![-1, goldenRatio, 0], ![-1, -goldenRatio, 0]}

/-- The rotations of the icosahedron: the rotations of space, orthogonal
matrices of determinant one, that carry every vertex to a vertex. -/
noncomputable def icoRotations : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {M | M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ ∀ v ∈ icoVertices, M.mulVec v ∈ icoVertices}

end Artform
