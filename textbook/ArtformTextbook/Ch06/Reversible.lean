import Mathlib.Tactic.Abel
import ArtformTextbook.Ch06.Statements

/-!
# Reversibility of the Maxwell tick (Theorem 6.1)

The macro-tick is the Ampère kick followed by the Faraday move. Each phase
writes one channel from a function of the other alone, so each is undone by
subtraction, and the tick is undone by undoing the move first and then the
kick. No division is used, so the argument holds over `ZMod 8`.
-/

namespace Artform

/-- The inverse of the Maxwell macro-tick, as the proof of Theorem 6.1 unfolds
it: from `(A', E', ρ')` it first rebuilds the potential `A = A' + E'`, then
sets `E = E' − curl*(curl A) + J` and `ρ = ρ' + div J`. -/
private def maxwellUntick (K : Canvas) (J : K.E → ZMod 8) (s : MaxwellState K) :
    MaxwellState K :=
  let A := s.A + s.E
  ⟨A, s.E - K.curlStar (K.curl A) + J, s.ρ + K.div J⟩

/-- **Theorem 6.1** (reversibility). For fixed source current `J`, the Maxwell
macro-tick is bijective: `maxwellUntick` undoes it on either side. -/
@[book "thm:reversible"]
theorem reversible : Statement.reversible := by
  intro K J
  refine Function.bijective_iff_has_inverse.mpr
    ⟨maxwellUntick K J, fun s => ?_, fun s => ?_⟩
  · -- Undoing a tick: `A' + E'` is the old potential, so the old curvature is
    -- read again, and taking its kick back returns the old electric links.
    obtain ⟨A, E, ρ⟩ := s
    simp only [maxwellTick, maxwellUntick, sub_add_cancel]
    congr 1
    abel
  · -- Ticking after undoing: every channel comes back.
    obtain ⟨A, E, ρ⟩ := s
    simp only [maxwellTick, maxwellUntick]
    congr 1 <;> abel

end Artform
