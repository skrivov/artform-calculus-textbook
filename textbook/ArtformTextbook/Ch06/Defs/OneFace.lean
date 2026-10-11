import Mathlib.Data.Fin.VecNotation
import ArtformTextbook.Ch03.Defs.Canvas

/-!
# The one face of Figure 6.7

The smallest canvas with a face: one square, its corners `c₁, …, c₄` the
vertices `0, …, 3` and its links `ℓ₁, …, ℓ₄` the edges `0, …, 3`, each stored
anticlockwise round the face, `ℓᵢ` from `cᵢ` to `cᵢ₊₁`. Figures 6.7 to 6.9 and
the checkpoints after them run the Maxwell tick on it.
-/

namespace Artform

/-- The one face of Figure 6.7, its four links stored anticlockwise round it. -/
abbrev oneFace : Canvas where
  V := Fin 4
  E := Fin 4
  F := Fin 1
  src := ![0, 1, 2, 3]
  tgt := ![1, 2, 3, 0]
  boundary _ := [(0, true), (1, true), (2, true), (3, true)]
  closed _ := by unfold IsClosedWalk; decide

end Artform
