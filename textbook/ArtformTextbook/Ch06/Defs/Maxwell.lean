import Mathlib.Data.ZMod.Defs
import ArtformTextbook.Ch05.Defs.Calculus

/-!
# The reversible Maxwell tick (Sections 6.2 and 6.3)

The fields of the toy electrodynamics live on a canvas, with every value
modulo eight.
-/

namespace Artform

/-- A state of the toy electrodynamics on a canvas `K`: the link potential `A`
and the electric links `E`, one value at every edge in its stored direction,
and the charges `ρ` at the sites; every value modulo eight. -/
structure MaxwellState (K : Canvas) where
  /-- The link potential. -/
  A : K.E → ZMod 8
  /-- The electric links. -/
  E : K.E → ZMod 8
  /-- The charges at the sites. -/
  ρ : K.V → ZMod 8

/-- The Maxwell macro-tick (Section 6.3) for a fixed source current `J`. First
the Ampère kick writes `E' = E + curl*(B) − J` with `B = curl A`, the
pre-tick curvature, and the charge update is continuity, `ρ' = ρ − div J`;
then the Faraday move writes `A' = A − E'`. -/
def maxwellTick (K : Canvas) (J : K.E → ZMod 8) (s : MaxwellState K) : MaxwellState K :=
  let E' := s.E + K.curlStar (K.curl s.A) - J
  ⟨s.A - E', E', s.ρ - K.div J⟩

end Artform
