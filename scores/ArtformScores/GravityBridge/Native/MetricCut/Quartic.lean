import ArtformScores.GravityBridge.Native.MetricCut.QuarticStatements
/-! # The supplied native quartic contacts with both elimination returns -/
namespace Artform.Scores.GravityBridge.Native.MetricCut
open Matrix
open Matrix
lemma quartic_visible_return (T phi : ℚ) :
    visibleFourthDivergence T phi = -quarticRawConstant*T*phi := by
  norm_num [visibleFourthDivergence, normalFourthDivergence, fullThirdSourceDerivative,
    dependentFourth, quarticRawConstant, nativeKappa, nativeA, nativeE, nativeHd, nativeD]
  ring
lemma quartic_constant_guards :
    nativeBeta < 0 ∧ nativeHd ≠ 0 ∧ nativeD ≠ 0 ∧
    nativeKappa/24 < quarticConstant ∧ 0 < quarticConstant := by
  norm_num [quarticConstant, quarticRawConstant, quarticTopReturn, nativeKappa, nativeA,
    nativeG, nativeE, nativeHd, nativeD, nativeBeta]
-- Bilinear transpose: both factors have -i, without conjugating the second.
lemma cubic_top_return (rho : ℂ) (v : SVec ℂ) (hr : rho ≠ 0) :
    dot3 (cubicColumn rho v) (topInverse rho (cubicColumn rho v)) =
      (quarticTopReturn : ℂ)*dot3 v v := by
  have hleft (a : ℂ) (x y : SVec ℂ) : dot3 (a • x) y = a * dot3 x y := by
    rw [dot3_symm, dot3_smul, dot3_symm]
  simp only [cubicColumn, topInverse, dot3_smul, hleft]
  norm_num [quarticTopReturn, nativeKappa, nativeG, nativeA, nativeBeta]
  field_simp
  ring_nf
  norm_num
lemma quartic_scalar_after_both_returns (a rho w : ℂ) (hr : rho ≠ 0) :
    (-(quarticRawConstant : ℂ) * (-rho^2*w) * (a/(Complex.I*rho))) /
      (Complex.I*rho) - (quarticTopReturn : ℂ)*w*a =
      -(quarticConstant : ℂ)*w*a := by
  simp only [quarticConstant, Rat.cast_add]
  field_simp
  ring_nf
  norm_num
-- This is the native angular expression in fixed original spatial coordinates.
lemma angular_nonnegative (k : SVec ℝ) : 0 ≤ angularSquare k := by
  unfold angularSquare dot3
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
lemma quartic_strict_on_patch (k : SVec ℝ) (hgap : 0 < angularSquare k) :
    quarticScalar k < 0 := by
  have hc : (0 : ℝ) < (quarticConstant : ℝ) := by
    exact_mod_cast quartic_constant_guards.2.2.2.2
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hgap
/-- **GAC2:quartic-two-return-coefficient**
(the supplied native quartic contacts with both elimination returns). -/
@[ledger "GAC2:quartic-two-return-coefficient"]
theorem quarticLaw : Statement.quarticLaw := by
  
  exact ⟨quartic_visible_return,
    quartic_constant_guards,
    cubic_top_return,
    quartic_scalar_after_both_returns,
    angular_nonnegative,
    quartic_strict_on_patch⟩
/-! ## Non-vacuity -/
example : angularSquare (![1, 2, 3] : SVec ℝ) = 38/7 ∧
    quarticScalar (![1, 2, 3] : SVec ℝ) < 0 := by
  have ha : angularSquare (![1, 2, 3] : SVec ℝ) = 38/7 := by
    norm_num [angularSquare, angularVector, projector3, outer3, rho2, dot3,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  refine ⟨ha, quartic_strict_on_patch _ ?_⟩
  rw [ha]
  norm_num
end Artform.Scores.GravityBridge.Native.MetricCut
