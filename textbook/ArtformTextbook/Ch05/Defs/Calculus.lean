import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Int.Defs
import ArtformTextbook.Ch03.Defs.Canvas

/-!
# Difference, curl and divergence on a canvas (Section 5.10)

A site field has one coefficient at every vertex, a link field one at every
edge in its stored direction (the other traversal carries minus it), and a
face field one at every face. Coefficients lie in a commutative ring `R`.
-/

namespace Artform.Canvas

open scoped BigOperators

variable (K : Canvas) {R : Type*} [CommRing R]

-- ANCHOR: lcalculus
/-- The difference `Dφ(u → v) = φ(v) − φ(u)` along each edge, `d₀ = D₀ᵀ`. -/
def diff (φ : K.V → R) : K.E → R := fun e => φ (K.tgt e) - φ (K.src e)

/-- The curl: on each face, the signed sum of the link values round its
boundary, read anticlockwise, `d₁ = D₁ᵀ`. -/
def curl (A : K.E → R) : K.F → R := fun f => ∑ e, (K.inc e f : R) * A e

/-- The divergence: at each vertex, what leaves along the links minus what
arrives, `div = −D₀`. -/
def div (E : K.E → R) : K.V → R := fun v =>
  ∑ e, ((if K.src e = v then E e else 0) - (if K.tgt e = v then E e else 0))

/-- The adjoint curl, which sends a face value to its boundary links with the
boundary signs, `curl* = D₁`. -/
def curlStar (B : K.F → R) : K.E → R := fun e => ∑ f, (K.inc e f : R) * B f
-- ANCHOR_END: lcalculus

end Artform.Canvas
