import Mathlib.Combinatorics.SimpleGraph.Metric
import ArtformTextbook.Ch03.Defs.Canvas
import ArtformTextbook.Ch05.Defs.Laws

/-!
# Local laws and halos (*What a law says*)

Definition 5.2: a deterministic law on a canvas is local when the new value at
each cell depends only on the old values at the cells within a fixed number of
edges of it, the cell's halo.

The cells here are the vertices of the canvas, and the number of edges between
two vertices is the length of a shortest path of edges joining them
(`SimpleGraph.edist`, infinite when none does). A table gives each vertex a
value of its own type.
-/

namespace Artform

namespace Canvas

/-- The graph of the vertices of a canvas: two vertices are adjacent when an
edge joins them. -/
def vertexGraph (K : Canvas) : SimpleGraph K.V :=
  SimpleGraph.fromRel fun v w => ∃ e, K.src e = v ∧ K.tgt e = w

/-- **Definition 5.2** (halo): the vertices within `r` edges of the vertex
`v`. -/
@[book "def:local-law"]
def halo (K : Canvas) (r : ℕ) (v : K.V) : Set K.V := {w | K.vertexGraph.edist v w ≤ r}

theorem mem_halo_self (K : Canvas) (r : ℕ) (v : K.V) : v ∈ K.halo r v := by
  simp [halo]

end Canvas

/-- **Definition 5.2** (local law): a deterministic law on the tables over the
vertices of the canvas `K` is local when there is a fixed number `r` of edges
such that the new value at each vertex depends only on the old values in its
halo of radius `r`. -/
@[book "def:local-law"]
def DetLaw.IsLocal {K : Canvas} {Val : K.V → Type*} (L : DetLaw ((v : K.V) → Val v)) : Prop :=
  ∃ r : ℕ, ∀ (v : K.V) (x y : (w : K.V) → Val w),
    (∀ w ∈ K.halo r v, x w = y w) → L.tick x v = L.tick y v

/-! ## Non-vacuity -/

/-- A law that changes every value by a rule read at the vertex alone is local,
with halos of radius `0`. -/
example (K : Canvas) (g : K.V → ℤ → ℤ) :
    (⟨fun x v => g v (x v)⟩ : DetLaw (K.V → ℤ)).IsLocal :=
  ⟨0, fun v x y h => by
    change g v (x v) = g v (y v)
    rw [h v (K.mem_halo_self 0 v)]⟩

end Artform
