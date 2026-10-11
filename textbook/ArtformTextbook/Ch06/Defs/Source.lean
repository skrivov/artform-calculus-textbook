import ArtformTextbook.Ch05.Defs.Laws
import ArtformTextbook.Ch06.Defs.Maxwell

/-!
# The Maxwell state with its source, and the gauge action on states

Theorem 6.1 fixes the source current `J` and ticks the state `(A, E, ρ)`. The
time reversal of Corollary 6.2 turns the current round, so there the state
carries `J` as well: the frame of the Maxwell law holds `A`, `E` and the
source `J` on the links and `ρ` at the sites, and no move writes `J`
(Section 6.3, "Locality and parallelism"). The tick reads the current from the
state and carries it unchanged.
-/

namespace Artform

/-- A state of the Maxwell frame with its source: the potential `A`, the
electric links `E` and the current `J`, one value at every edge in its stored
direction, and the charges `ρ` at the sites; every value modulo eight. -/
@[ext]
structure MaxwellSourceState (K : Canvas) where
  /-- The link potential. -/
  A : K.E → ZMod 8
  /-- The electric links. -/
  E : K.E → ZMod 8
  /-- The source current. -/
  J : K.E → ZMod 8
  /-- The charges at the sites. -/
  ρ : K.V → ZMod 8

/-- The Maxwell macro-tick on states that carry their source: the macro-tick of
Section 6.3 for the current `J` that the state holds, which it carries
unchanged. So `E' = E + curl*(curl A) − J`, `A' = A − E'`, `J' = J` and
`ρ' = ρ − div J`. -/
def maxwellSourceTick (K : Canvas) (s : MaxwellSourceState K) : MaxwellSourceState K :=
  let s' := maxwellTick K s.J ⟨s.A, s.E, s.ρ⟩
  ⟨s'.A, s'.E, s.J, s'.ρ⟩

/-- The Maxwell law on states that carry their source, as a deterministic law
(Definition 5.1): its tick is `maxwellSourceTick`. -/
def maxwellSourceLaw (K : Canvas) : DetLaw (MaxwellSourceState K) := ⟨maxwellSourceTick K⟩

/-- The time reversal of Corollary 6.2: `I(A, E, J, ρ) = (−A − E, E, −J, ρ)`. -/
def maxwellTimeReversal (K : Canvas) (s : MaxwellSourceState K) : MaxwellSourceState K :=
  ⟨-s.A - s.E, s.E, -s.J, s.ρ⟩

/-- The gauge action `A ↦ A + Dg` of `eq:gauge-formula` on a state
`(A, E, ρ)`, for a site function `g`: it adds the difference `Dg` to the
potential and fixes `E` and `ρ`. -/
def MaxwellState.gauge {K : Canvas} (g : K.V → ZMod 8) (s : MaxwellState K) :
    MaxwellState K :=
  ⟨s.A + K.diff g, s.E, s.ρ⟩

end Artform
