import ArtformTextbook.Ch05.Defs.Affine

/-!
# The current of a tally (Section 5.3)

The additive part of an affine law written cell by cell,
`M(p)(v) = Σ_u M_{vu} p(u)`, and the current a kept tally carries along it.
-/

namespace Artform.AffineLaw

variable {C : Type*} [DecidableEq C] {n : ℕ}

/-- `M_{vu}`: the number that the new value at `v` takes from the old value at
`u`, read off the table with a single `1` at `u`. -/
def coeff (L : AffineLaw C n) (v u : C) : ZMod n := L.M (Pi.single u 1) v

/-- The current `J_{u→v}(p) = d(v) M_{vu} p(u)` of the tally with weights `d`. -/
def current (L : AffineLaw C n) (d : C → ZMod n) (u v : C) (p : C → ZMod n) : ZMod n :=
  d v * L.coeff v u * p u

end Artform.AffineLaw
