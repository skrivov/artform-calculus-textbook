import ArtformScores.GravityBridge.Native.SelectedJets.RecurrencesDefs

/-! # Unique coupled selected-jet recurrences for the fixed reference -/

namespace Artform.Scores.GravityBridge.Native.SelectedJets.Statement

open Matrix

/-- **GAC2:selected-jet-coupled-recurrences**
(unique coupled selected-jet recurrences for the fixed reference). -/
@[ledger "GAC2:selected-jet-coupled-recurrences"]
def recurrencesLaw : Prop :=
    (principal * principalInverse = 1 ∧ principalInverse * principal = 1) ∧
    (∀ (y : Vec3) (_hy : principal *ᵥ y = (101 / 490 : ℚ) • selectedU),
    y = selectedJet.y) ∧
    (jetEquations selectedJet) ∧
    (∀ (s : SelectedJet) (_hs : jetEquations s),
    s = selectedJet)

end Artform.Scores.GravityBridge.Native.SelectedJets.Statement
