import ArtformScores.GravityBridge.Native.LongitudinalRecipe.ContactDefs

/-! # A quantitative temporal-contact test for the supplied fixed recipe -/

namespace Artform.Scores.GravityBridge.Native.LongitudinalRecipe.Statement

open Matrix
open MetricCut

/-- **GAC2:fixed-recipe-contact-budget**
(a quantitative temporal-contact test for the supplied fixed recipe). -/
@[ledger "GAC2:fixed-recipe-contact-budget"]
def contactLaw : Prop :=
    (referenceQuartic ≠ 0) ∧
    (referenceBoostCoefficient ≠ 0) ∧
    (∀ (h M : ℝ) (c error : ℂ)
    (_he : ‖error‖ ≤ M * |h| ^ 3),
    |h| ^ 2 * (‖c‖-M * |h|) ≤ ‖(h : ℂ) ^ 2 * c + error‖) ∧
    (∀ (h M : ℝ) (c error : ℂ) (_hh : h ≠ 0)
    (_he : ‖error‖ ≤ M * |h| ^ 3) (_hs : M * |h| < ‖c‖),
    (h : ℂ) ^ 2 * c + error ≠ 0) ∧
    (∀ (h M : ℝ) (c error : ℂ) (_hh : h ≠ 0)
    (_he : ‖error‖ ≤ M * |h| ^ 3) (_hs : M * |h| < ‖c‖),
    -(h : ℂ) * ((h : ℂ) ^ 2 * c + error) ≠ 0) ∧
    (∀ (h M : ℝ) (error : ℂ) (_hh : h ≠ 0)
    (_he : ‖error‖ ≤ M * |h| ^ 3) (_hs : M * |h| < ‖referenceBoostCoefficient‖),
    (h : ℂ) ^ 2 * referenceBoostCoefficient + error ≠ 0 ∧
    -(h : ℂ) * ((h : ℂ) ^ 2 * referenceBoostCoefficient + error) ≠ 0)

end Artform.Scores.GravityBridge.Native.LongitudinalRecipe.Statement
