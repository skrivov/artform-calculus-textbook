import ArtformScores.GravityBridge.Native.LongitudinalRecipe.ContactStatements

/-! # A quantitative temporal-contact test for the supplied fixed recipe -/

namespace Artform.Scores.GravityBridge.Native.LongitudinalRecipe

open Matrix
open MetricCut



open MetricCut

lemma reference_quartic_nonzero : referenceQuartic ≠ 0 := by
  unfold referenceQuartic
  exact mul_ne_zero (by norm_num) (ne_of_gt quartic_constant_guards.2.2.2.2)

lemma fixed_recipe_boost_nonzero : referenceBoostCoefficient ≠ 0 := by
  unfold referenceBoostCoefficient
  apply div_ne_zero
  · have ht : ((total : ℚ) : ℂ) ≠ 0 := by exact_mod_cast recipe_total_nonzero
    exact neg_ne_zero.mpr ht
  · apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
    · exact_mod_cast reference_quartic_nonzero

lemma actual_contact_lower_bound (h M : ℝ) (c error : ℂ)
    (he : ‖error‖ ≤ M * |h| ^ 3) :
    |h| ^ 2 * (‖c‖-M * |h|) ≤ ‖(h : ℂ) ^ 2 * c + error‖ := by
  have hb : ‖(h : ℂ) ^ 2 * c‖ ≤ ‖(h : ℂ) ^ 2 * c + error‖ + ‖error‖ := by
    have hx := norm_add_le ((h : ℂ) ^ 2 * c + error) (-error)
    simpa only [add_neg_cancel_right, norm_neg] using hx
  have hn : ‖(h : ℂ) ^ 2 * c‖ = |h| ^ 2 * ‖c‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [hn] at hb
  nlinarith

lemma actual_contact_nonzero (h M : ℝ) (c error : ℂ) (hh : h ≠ 0)
    (he : ‖error‖ ≤ M * |h| ^ 3) (hs : M * |h| < ‖c‖) :
    (h : ℂ) ^ 2 * c + error ≠ 0 := by
  have hp : 0 < |h| ^ 2 * (‖c‖-M * |h|) :=
    mul_pos (sq_pos_of_ne_zero (abs_ne_zero.mpr hh)) (sub_pos.mpr hs)
  have hl := actual_contact_lower_bound h M c error he
  intro hz
  rw [hz, norm_zero] at hl
  exact (not_le_of_gt hp) hl

lemma native_log_contact_nonzero (h M : ℝ) (c error : ℂ) (hh : h ≠ 0)
    (he : ‖error‖ ≤ M * |h| ^ 3) (hs : M * |h| < ‖c‖) :
    -(h : ℂ) * ((h : ℂ) ^ 2 * c + error) ≠ 0 := by
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (by exact_mod_cast hh)
  · exact actual_contact_nonzero h M c error hh he hs

-- A fixed admitted coefficient still needs an actual uniform remainder bound.
lemma fixed_recipe_finite_spacing_obstruction (h M : ℝ) (error : ℂ) (hh : h ≠ 0)
    (he : ‖error‖ ≤ M * |h| ^ 3) (hs : M * |h| < ‖referenceBoostCoefficient‖) :
    (h : ℂ) ^ 2 * referenceBoostCoefficient + error ≠ 0 ∧
    -(h : ℂ) * ((h : ℂ) ^ 2 * referenceBoostCoefficient + error) ≠ 0 :=
  ⟨actual_contact_nonzero h M _ error hh he hs,
    native_log_contact_nonzero h M _ error hh he hs⟩

/-- **GAC2:fixed-recipe-contact-budget**
(a quantitative temporal-contact test for the supplied fixed recipe). -/
@[ledger "GAC2:fixed-recipe-contact-budget"]
theorem contactLaw : Statement.contactLaw := by
  exact ⟨reference_quartic_nonzero,
    fixed_recipe_boost_nonzero,
    actual_contact_lower_bound,
    actual_contact_nonzero,
    native_log_contact_nonzero,
    fixed_recipe_finite_spacing_obstruction⟩

/-! ## Non-vacuity -/

example : referenceBoostCoefficient ≠ 0 ∧
    (1 : ℂ) ^ 2 * referenceBoostCoefficient + 0 ≠ 0 := by
  refine ⟨fixed_recipe_boost_nonzero, ?_⟩
  apply actual_contact_nonzero 1 0 _ 0 (by norm_num)
  · norm_num
  · simpa using norm_pos_iff.mpr fixed_recipe_boost_nonzero

end Artform.Scores.GravityBridge.Native.LongitudinalRecipe
