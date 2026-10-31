import ArtformScores.GravityBridge.Native.TTCoordinates.ProgramsStatements

/-! # Matched exact programs for the original temporal forcing -/

namespace Artform.Scores.GravityBridge.Native.TTCoordinates

open Matrix



open Matrix

lemma original_forcing_one_coordinate (q : Matrix (Fin 3) (Fin 3) ℚ)
    (hs : q.transpose = q) (ht : trace q = 0) (hk : q *ᵥ momentum = 0) :
    temporalSymbol momentum q = (84 / 505 : ℚ) * q 1 2 := by
  rw [complete_native_TT_parameterization q hs ht hk]
  rw [original_forcing_two_coordinates _ (parametric_TT_properties _ _).2.1]
  norm_num [parametricTT]
  ring

lemma literal_forcing_same_original (q : Matrix (Fin 3) (Fin 3) ℚ) :
    evalTTExpr q literalForcingProgram = temporalSymbol momentum q := by
  norm_num [evalTTExpr, literalForcingProgram, temporalSymbol, rhoSquared,
    diagonalContraction, momentum, Fin.sum_univ_succ]
  ring

lemma contracted_forcing_same_original (q : Matrix (Fin 3) (Fin 3) ℚ)
    (hs : q.transpose = q) (ht : trace q = 0) (hk : q *ᵥ momentum = 0) :
    evalTTExpr q contractedForcingProgram = temporalSymbol momentum q := by
  exact (original_forcing_one_coordinate q hs ht hk).symm

lemma forcing_program_costs :
    (ttScales literalForcingProgram, ttAdds literalForcingProgram) = (3, 2) ∧
    (ttScales contractedForcingProgram, ttAdds contractedForcingProgram) = (1, 0) := by
  decide +kernel

lemma no_free_matrix_wire (i j : Fin 3) (sign : ℚ) (hsgn : sign = 1 ∨ sign = -1) :
    ¬∀ (x y : ℚ), temporalSymbol momentum (parametricTT x y) = sign * parametricTT x y i j := by
  intro h
  have h0 := h 1 0
  rcases hsgn with rfl|rfl
  all_goals
    fin_cases i <;> fin_cases j <;>
      norm_num [temporalSymbol, rhoSquared, diagonalContraction, momentum, parametricTT,
      Fin.sum_univ_succ] at h0

lemma no_free_constant (c : ℚ) :
    ¬∀ (x y : ℚ), temporalSymbol momentum (parametricTT x y) = c := by
  intro h
  have h0 := h 0 0
  have h1 := h 1 0
  norm_num [temporalSymbol, rhoSquared, diagonalContraction, momentum, parametricTT,
    Fin.sum_univ_succ] at h0 h1
  linarith

/-- **GAC2:native-tt-forcing-programs**
(matched exact programs for the original temporal forcing). -/
@[ledger "GAC2:native-tt-forcing-programs"]
theorem programsLaw : Statement.programsLaw := by
  exact ⟨original_forcing_one_coordinate,
    literal_forcing_same_original,
    contracted_forcing_same_original,
    forcing_program_costs,
    no_free_matrix_wire,
    no_free_constant⟩

/-! ## Non-vacuity -/

example : evalTTExpr polarization contractedForcingProgram = 36 / 505 ∧
    evalTTExpr (parametricTT 0 1) contractedForcingProgram = 7 / 101 := by
  constructor
  · norm_num [evalTTExpr, contractedForcingProgram, polarization]
  · norm_num [evalTTExpr, contractedForcingProgram, parametricTT]

end Artform.Scores.GravityBridge.Native.TTCoordinates
