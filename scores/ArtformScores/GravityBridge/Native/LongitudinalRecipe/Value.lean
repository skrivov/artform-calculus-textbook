import ArtformScores.GravityBridge.Native.LongitudinalRecipe.ValueStatements

/-! # Exact value and regular-prime replay of the supplied four-group recipe -/

namespace Artform.Scores.GravityBridge.Native.LongitudinalRecipe

open Matrix

variable {K : Type*} [Field K]

open Matrix
lemma recipe_is_unique_selected_jet : recipeJet = SelectedJets.selectedJet := by
  apply SelectedJets.SelectedJet.ext <;> rfl

lemma recipe_satisfies_coupled_equations : SelectedJets.jetEquations recipeJet := by
  rw [recipe_is_unique_selected_jet]
  exact SelectedJets.selected_jet_solves

lemma recipe_denominator_guards :
    (∀ n ∈ denominatorSites, n ≠ 0 ∧ (n : ZMod 13) ≠ 0) ∧
    (hd : ℚ) ≠ 0 ∧ (dd : ℚ) ≠ 0 ∧ (hd : ZMod 13) ≠ 0 ∧ (dd : ZMod 13) ≠ 0 := by
  decide +kernel

lemma recipe_total_value : (total : ℚ) = 42464891403943157 / 1369394558168868000 := by
  norm_num [total, allGroups, group2, group3, group4, group5, fullThirdSourceDerivative,
    hMoment, bMoment, cMoment, dMoment, rz, a5, c4, bc4, b4, l5, l4e, l4s, p1, p2, n1, n2, w1, w2,
    m1, m2, m3, moment, selectedY, inversePrincipal, outerK, forcingU, k, kap, aa, gg, ee, hd, dd,
    betaPhysical, betaThird, bb, cv, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

lemma recipe_total_nonzero : (total : ℚ) ≠ 0 := by
  rw [recipe_total_value]
  norm_num

lemma recipe_residue_groups : (allGroups : Fin 4 → ZMod 13) = ![0, 3, 3, 9] := by
  decide +kernel

lemma recipe_residue_total : (total : ZMod 13) = 2 := by
  decide +kernel

/-- **GAC2:four-group-recipe-exact-value**
(exact value and regular-prime replay of the supplied four-group recipe). -/
@[ledger "GAC2:four-group-recipe-exact-value"]
theorem valueLaw : Statement.valueLaw := by
  exact ⟨recipe_is_unique_selected_jet,
    recipe_satisfies_coupled_equations,
    recipe_denominator_guards,
    recipe_total_value,
    recipe_total_nonzero,
    recipe_residue_groups,
    recipe_residue_total⟩

/-! ## Non-vacuity -/

example : (total : ℚ) ≠ 0 ∧ (total : ZMod 13) = 2 :=
  ⟨recipe_total_nonzero, recipe_residue_total⟩

end Artform.Scores.GravityBridge.Native.LongitudinalRecipe
