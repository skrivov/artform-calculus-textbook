import ArtformScores.GravityBridge.Native.Full40.FourDirectionDefs

/-! # A noncollapsed four-shift finite periodic force test -/

namespace Artform.Scores.GravityBridge.Native.Full40.Statement

/-- **GAC2:four-shift-original-force-test**
(a noncollapsed four-shift finite periodic force test). -/
@[ledger "GAC2:four-shift-original-force-test"]
def fourDirectionLaw : Prop :=
    (completeQuadratic testStep (1 / 101) fullPulse = 12 / 101) ∧
    (nativeFirstVariation testStep (1 / 101) fullPulse (originTest 0) = 12 / 101 ∧
    nativeFirstVariation testStep (1 / 101) fullPulse (originTest 16) = -2 / 101 ∧
    nativeFirstVariation testStep (1 / 101) fullPulse (originTest 39) = 0) ∧
    (∀ i j : Fin 4, i ≠ j →
    
    testStep i ≠ 0 ∧ testStep i ≠ testStep j ∧ testStep i + testStep j ≠ 0) ∧
    (∀ i : Fin 4,
    (fullPulse (0 + testStep i)).1 i i - (fullPulse 0).1 i i = -1) ∧
    (fullForce testStep (1 / 101 : ℚ) fullPulse (0, Sum.inl (0, 0)) = 12 / 101 ∧
    fullForce testStep (1 / 101 : ℚ) fullPulse (0, Sum.inr (0, 0)) = -2 / 101)

end Artform.Scores.GravityBridge.Native.Full40.Statement
