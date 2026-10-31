import ArtformScores.GravityBridge.Native.RetroCertificates.PolynomialCostDefs

/-! # Exact degree-five inverse can cost more than block return -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates.Statement

open Matrix Full40 TTCross Retrospective

/-- **GAC2:native-polynomial-work-audit**
(exact degree-five inverse can cost more than block return). -/
@[ledger "GAC2:native-polynomial-work-audit"]
def polynomialCostLaw : Prop :=
    ((∀ s : Fin 4, ∀ i j : Fin 3, distinctB (K := ℚ) s i j ≠ 0) ∧
    (∀ b : Fin 4, ∀ i j : Fin 3, repeatB (K := ℚ) b i j ≠ 0)) ∧
    (∀ (A : Connection ℚ),
    (nativeRun oddNativeProgram A).getD 9 0 = fullHApply A) ∧
    (nativeValid 0 oddNativeProgram = true ∧
    nativeScaleCost oddNativeProgram = 432 ∧ nativeAddCost oddNativeProgram = 288) ∧
    (∀ (cs ca : ℚ) (_hs : 0 < cs) (_ha : 0 ≤ ca),
    (fullScaleCount true : ℚ) * cs + (fullAddCount true : ℚ) * ca <
      (nativeScaleCost oddNativeProgram : ℚ) * cs + (nativeAddCost oddNativeProgram : ℚ) * ca)

end Artform.Scores.GravityBridge.Native.RetroCertificates.Statement
