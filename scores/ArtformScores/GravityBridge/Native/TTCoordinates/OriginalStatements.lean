import ArtformScores.GravityBridge.Native.TTCoordinates.OriginalDefs

/-! # The complete original TT plane and temporal witness -/

namespace Artform.Scores.GravityBridge.Native.TTCoordinates.Statement

open Matrix

/-- **GAC2:original-native-tt-plane**
(the complete original tt plane and temporal witness). -/
@[ledger "GAC2:original-native-tt-plane"]
def originalLaw : Prop :=
    (dyadPolarization = polarization) ∧
    (frobeniusSquare polarization = 2) ∧
    (∀ (x y : ℚ),
    (parametricTT x y).transpose = parametricTT x y ∧ trace (parametricTT x y) = 0 ∧
    parametricTT x y *ᵥ momentum = 0) ∧
    (∀ (q : Matrix (Fin 3) (Fin 3) ℚ)
    (_hs : q.transpose = q) (_ht : trace q = 0) (_hk : q *ᵥ momentum = 0),
    q = parametricTT (q 0 0) (q 1 1)) ∧
    (∀ (q : Matrix (Fin 3) (Fin 3) ℚ)
    (_ht : trace q = 0),
    temporalSymbol momentum q = (14 / 101 : ℚ) * q 0 0 + (7 / 101 : ℚ) * q 1 1) ∧
    (polarization = parametricTT (47 / 70) (-22 / 70) ∧
    temporalSymbol momentum dyadPolarization = 36 / 505)

end Artform.Scores.GravityBridge.Native.TTCoordinates.Statement
