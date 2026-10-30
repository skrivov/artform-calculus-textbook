import ArtformScores.GravityBridge.Native.Statements

/-! # An exact rational witness for the leading lower temporal symbol -/

namespace Artform.Scores.GravityBridge.Native

open Matrix

/-- **GAC:temporal-witness** (a rational transverse traceless symbol witness). -/
@[ledger "GAC:temporal-witness"]
theorem temporalWitness : Statement.temporalWitness := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [polarization, Matrix.transpose_apply]
  · norm_num [polarization, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;>
      norm_num [polarization, momentum, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [rhoSquared, momentum, Fin.sum_univ_succ]
  · norm_num [diagonalContraction, momentum, polarization, Fin.sum_univ_succ]
  · norm_num [temporalSymbol, rhoSquared, diagonalContraction, momentum,
      polarization, Fin.sum_univ_succ]
  · norm_num [temporalSymbol, rhoSquared, diagonalContraction, momentum,
      polarization, Fin.sum_univ_succ]

/-! ## Non-vacuity -/

/-- All three spatial momentum components and the response are nonzero. -/
example : (∀ j, momentum j ≠ 0) ∧ temporalSymbol momentum polarization ≠ 0 := by
  constructor
  · intro j
    fin_cases j <;> norm_num [momentum]
  · exact temporalWitness.2.2.2.2.2.2

end Artform.Scores.GravityBridge.Native
