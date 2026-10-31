import ArtformScores.GravityBridge.Native.TTCoordinates.HeldoutDefs

/-! # A second off-axis native temporal forcing test -/

namespace Artform.Scores.GravityBridge.Native.TTCoordinates.Statement

open Matrix

/-- **GAC2:heldout-native-tt-force**
(a second off-axis native temporal forcing test). -/
@[ledger "GAC2:heldout-native-tt-force"]
def heldoutLaw : Prop :=
    (heldoutPolarization = heldoutDyad) ∧
    (heldoutPolarization.transpose = heldoutPolarization ∧ trace heldoutPolarization = 0 ∧
    heldoutPolarization *ᵥ heldoutMomentum = 0 ∧
    (∑ i, ∑ j, (heldoutPolarization i j) ^ 2) = 2 ∧
    temporalSymbol heldoutMomentum heldoutPolarization = 59 / 505) ∧
    (∀ (q : Matrix (Fin 3) (Fin 3) ℚ) (_ht : trace q = 0),
    temporalSymbol heldoutMomentum q = (63 / 202 : ℚ) * q 0 0 + (42 / 202 : ℚ) * q 1 1) ∧
    (temporalSymbol heldoutMomentum heldoutPolarization≠0)

end Artform.Scores.GravityBridge.Native.TTCoordinates.Statement
