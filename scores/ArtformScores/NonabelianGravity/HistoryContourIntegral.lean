import ArtformScores.NonabelianGravity.HistoryContour

/-! # Actual Lebesgue contour integrals, with declared certificate-coordinate volume -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
open HistoryGaussian MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Matrix ι ι ℚ} (c : Certificate H)

noncomputable def stationary (E : ℚ) (r : ι → ℚ) : ℚ := E - (1 / 2) * sourceContact c r

noncomputable def contourExponent (E : ℚ) (r : ι → ℚ) (ℏ : ℝ) (t : Active c → ℝ) : ℂ :=
  Complex.I * ((E : ℂ) + complexAction (H := H) (fun i => (r i : ℂ)) (contour c r t)) / ℏ

lemma exponent_completion (E : ℚ) (r : ι → ℚ) (ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (t : Active c → ℝ) :
    contourExponent c E r ℏ t = Complex.I * (stationary c E r : ℂ) / ℏ -
      ∑ i : Active c, ((|activeDiagonal c i| / (2 * ℏ) : ℝ) : ℂ) * (t i : ℂ) ^ 2 := by
  let q : Active c → ℂ := fun i => (c.diagonal i : ℂ) / 2 * contourCoordinates c r t i ^ 2 -
    (transformedSource c r i : ℂ) * contourCoordinates c r t i
  let contact : Active c → ℂ := fun i =>
    (transformedSource c r i : ℂ) ^ 2 / (c.diagonal i : ℂ)
  let weight : Active c → ℂ := fun i =>
    ((|activeDiagonal c i| / (2 * ℏ) : ℝ) : ℂ) * (t i : ℂ) ^ 2
  have hp (i : Active c) : Complex.I * q i / ℏ =
      (-Complex.I / (2 * (ℏ : ℂ))) * contact i - weight i := by
    rw [show q i = (c.diagonal i : ℂ) / 2 * contourCoordinates c r t i ^ 2 -
      (transformedSource c r i : ℂ) * contourCoordinates c r t i from rfl,
      contour_coordinate_completion c r ℏ hℏ t i]
    dsimp [contact, weight]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hs : (∑ i : Active c, Complex.I * q i / ℏ) =
      ∑ i : Active c, ((-Complex.I / (2 * (ℏ : ℂ))) * contact i - weight i) :=
    Finset.sum_congr rfl (fun i _ => hp i)
  have hleft : (∑ i : Active c, Complex.I * q i / ℏ) = Complex.I * (∑ i, q i) / ℏ := by
    simp only [Finset.mul_sum, Finset.sum_div]
  have hright : (∑ i : Active c, ((-Complex.I / (2 * (ℏ : ℂ))) * contact i - weight i)) =
      (-Complex.I / (2 * (ℏ : ℂ))) * (∑ i, contact i) - ∑ i, weight i := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hleft, hright] at hs
  have hc : (sourceContact c r : ℂ) = ∑ i : Active c, contact i := source_contact_active c r
  dsimp [contourExponent, contour]
  rw [restricted_diagonal_action]
  change Complex.I * ((E : ℂ) + ∑ i, q i) / ℏ = _
  simp only [stationary, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
  rw [hc]
  change Complex.I * ((E : ℂ) + ∑ i, q i) / ℏ =
    Complex.I * ((E : ℂ) - (1 / 2) * ∑ i, contact i) / ℏ - ∑ i, weight i
  linear_combination hs

lemma contour_phase_pullback (E : ℚ) (r : ι → ℚ) (ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (t : Active c → ℝ) :
    Complex.exp (contourExponent c E r ℏ t) =
      Complex.exp (Complex.I * (stationary c E r : ℂ) / ℏ) *
        (gaussian (activeDiagonal c) ℏ t : ℂ) := by
  rw [exponent_completion c E r ℏ hℏ t, sub_eq_add_neg, Complex.exp_add]
  congr 1
  rw [← Finset.sum_neg_distrib, Complex.exp_sum]
  simp only [gaussian, Complex.ofReal_prod, Complex.ofReal_exp]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  push_cast
  ring

lemma contour_integrable (E : ℚ) (r : ι → ℚ) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    Integrable (fun t : Active c → ℝ => Complex.exp (contourExponent c E r ℏ t)) := by
  simp_rw [contour_phase_pullback c E r ℏ (ne_of_gt hℏ)]
  exact ((gaussian_integrable (activeDiagonal c) ℏ hℏ (active_diagonal_ne c)).ofReal).const_mul _

lemma contour_integral (E : ℚ) (r : ι → ℚ) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    (∫ t : Active c → ℝ, Complex.exp (contourExponent c E r ℏ t)) =
      Complex.exp (Complex.I * (stationary c E r : ℂ) / ℏ) *
        ((∏ i : Active c, Real.sqrt (Real.pi /
          (|activeDiagonal c i| / (2 * ℏ))) : ℝ) : ℂ) := by
  simp_rw [contour_phase_pullback c E r ℏ (ne_of_gt hℏ)]
  rw [integral_const_mul, integral_complex_ofReal, gaussian_integral]

end Artform.Scores.NonabelianGravity.HistoryElimination
