import ArtformScores.GravityBridge.Native.MetricCut.QuarticDefs
/-! # The supplied native quartic contacts with both elimination returns -/
namespace Artform.Scores.GravityBridge.Native.MetricCut.Statement
open Matrix
/-- **GAC2:quartic-two-return-coefficient**
(the supplied native quartic contacts with both elimination returns). -/
@[ledger "GAC2:quartic-two-return-coefficient"]
def quarticLaw : Prop :=
    (∀ (T phi : ℚ),
    visibleFourthDivergence T phi = -quarticRawConstant*T*phi) ∧
    (nativeBeta < 0 ∧ nativeHd ≠ 0 ∧ nativeD ≠ 0 ∧
    nativeKappa/24 < quarticConstant ∧ 0 < quarticConstant) ∧
    (∀ (rho : ℂ) (v : SVec ℂ) (_hr : rho ≠ 0),
    dot3 (cubicColumn rho v) (topInverse rho (cubicColumn rho v)) =
      (quarticTopReturn : ℂ)*dot3 v v) ∧
    (∀ (a rho w : ℂ) (_hr : rho ≠ 0),
    (-(quarticRawConstant : ℂ) * (-rho^2*w) * (a/(Complex.I*rho))) /
      (Complex.I*rho) - (quarticTopReturn : ℂ)*w*a =
      -(quarticConstant : ℂ)*w*a) ∧
    (∀ (k : SVec ℝ),
    0 ≤ angularSquare k) ∧
    (∀ (k : SVec ℝ) (_hgap : 0 < angularSquare k),
    quarticScalar k < 0)
end Artform.Scores.GravityBridge.Native.MetricCut.Statement
