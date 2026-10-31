import ArtformScores.GravityBridge.Native.RetroCertificates.PolynomialCostStatements

/-! # Exact degree-five inverse can cost more than block return -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective



open Matrix Full40 TTCross

set_option maxHeartbeats 1000000 in
-- Verify all72 declared dense macro coefficients are nonzero at fixed kappa.
lemma native_B_dense_macro_nonzero :
    (∀ s : Fin 4, ∀ i j : Fin 3, distinctB (K := ℚ) s i j ≠ 0) ∧
    (∀ b : Fin 4, ∀ i j : Fin 3, repeatB (K := ℚ) b i j ≠ 0) := by
  constructor <;> intro s i j <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [distinctB, spaceB, timeB, signS, repeatB, eta, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ]

lemma odd_native_program_original_output (A : Connection ℚ) :
    (nativeRun oddNativeProgram A).getD 9 0 = fullHApply A := by
  rw [← original_global_odd_inverse]
  rfl

lemma odd_native_program_cost : nativeValid 0 oddNativeProgram = true ∧
    nativeScaleCost oddNativeProgram = 432 ∧ nativeAddCost oddNativeProgram = 288 := by
  decide +kernel

lemma polynomial_route_more_work (cs ca : ℚ) (hs : 0 < cs) (ha : 0 ≤ ca) :
    (fullScaleCount true : ℚ) * cs + (fullAddCount true : ℚ) * ca <
      (nativeScaleCost oddNativeProgram : ℚ) * cs + (nativeAddCost oddNativeProgram : ℚ) * ca := by
  have hc := actual_all24_costs
  have hp := odd_native_program_cost
  rw [hc.2.2.2.2.1, hc.2.2.2.2.2, hp.2.1, hp.2.2]
  norm_num
  nlinarith

/-- **GAC2:native-polynomial-work-audit**
(exact degree-five inverse can cost more than block return). -/
@[ledger "GAC2:native-polynomial-work-audit"]
theorem polynomialCostLaw : Statement.polynomialCostLaw := by
  exact ⟨native_B_dense_macro_nonzero,
    odd_native_program_original_output,
    odd_native_program_cost,
    polynomial_route_more_work⟩

/-! ## Non-vacuity -/
example : (nativeRun oddNativeProgram (0 : Connection ℚ)).getD 9 0 = fullHApply 0 :=
  odd_native_program_original_output _

end Artform.Scores.GravityBridge.Native.RetroCertificates
