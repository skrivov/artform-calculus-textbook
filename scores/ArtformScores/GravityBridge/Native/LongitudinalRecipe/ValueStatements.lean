import ArtformScores.GravityBridge.Native.LongitudinalRecipe.ValueDefs

/-! # Exact value and regular-prime replay of the supplied four-group recipe -/

namespace Artform.Scores.GravityBridge.Native.LongitudinalRecipe.Statement

open Matrix

/-- **GAC2:four-group-recipe-exact-value**
(exact value and regular-prime replay of the supplied four-group recipe). -/
@[ledger "GAC2:four-group-recipe-exact-value"]
def valueLaw : Prop :=
    (recipeJet = SelectedJets.selectedJet) ∧
    (SelectedJets.jetEquations recipeJet) ∧
    ((∀ n ∈ denominatorSites, n ≠ 0 ∧ (n : ZMod 13) ≠ 0) ∧
    (hd : ℚ) ≠ 0 ∧ (dd : ℚ) ≠ 0 ∧ (hd : ZMod 13) ≠ 0 ∧ (dd : ZMod 13) ≠ 0) ∧
    ((total : ℚ) = 42464891403943157 / 1369394558168868000) ∧
    ((total : ℚ) ≠ 0) ∧
    ((allGroups : Fin 4 → ZMod 13) = ![0, 3, 3, 9]) ∧
    ((total : ZMod 13) = 2)

end Artform.Scores.GravityBridge.Native.LongitudinalRecipe.Statement
