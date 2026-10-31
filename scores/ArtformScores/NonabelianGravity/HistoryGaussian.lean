import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-! # Explicit absolutely convergent finite Gaussian reference measures

Lebesgue measure on the stated real coordinates is part of the definition.
This analytic lemma does not select a physical measure or handle a radical
by silently assigning it finite volume.
-/
set_option autoImplicit false
open MeasureTheory
namespace Artform.Scores.NonabelianGravity.HistoryGaussian
variable {ι : Type*} [Fintype ι]

noncomputable def gaussian (d : ι → ℝ) (ℏ : ℝ) (t : ι → ℝ) : ℝ :=
  ∏ i, Real.exp (-(|d i| / (2 * ℏ)) * t i ^ 2)

lemma gaussian_integrable (d : ι → ℝ) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (hd : ∀ i, d i ≠ 0) : Integrable (gaussian d ℏ) := by
  unfold gaussian
  change Integrable _ (Measure.pi (fun _ : ι => (volume : Measure ℝ)))
  apply Integrable.fintype_prod
    (f := fun i (x : ℝ) => Real.exp (-(|d i| / (2 * ℏ)) * x ^ 2))
  intro i
  exact integrable_exp_neg_mul_sq (div_pos (abs_pos.mpr (hd i)) (by positivity))

lemma gaussian_integral (d : ι → ℝ) (ℏ : ℝ) :
    (∫ t, gaussian d ℏ t) = ∏ i, Real.sqrt (Real.pi / (|d i| / (2 * ℏ))) := by
  unfold gaussian
  rw [integral_fintype_prod_volume_eq_prod
    (fun i (x : ℝ) => Real.exp (-(|d i| / (2 * ℏ)) * x ^ 2))]
  exact Finset.prod_congr rfl (fun i _ => integral_gaussian _)

noncomputable def reference (d : ι → ℝ) (ℏ stationary jacobian : ℝ)
    (phase : ℂ) : ℂ :=
  (jacobian : ℂ) * phase * Complex.exp (Complex.I * (stationary : ℂ) / ℏ) *
    ((∫ t, gaussian d ℏ t : ℝ) : ℂ)

lemma reference_formula (d : ι → ℝ) (ℏ stationary jacobian : ℝ) (phase : ℂ) :
    reference d ℏ stationary jacobian phase =
      (jacobian : ℂ) * phase * Complex.exp (Complex.I * (stationary : ℂ) / ℏ) *
        ((∏ i, Real.sqrt (Real.pi / (|d i| / (2 * ℏ))) : ℝ) : ℂ) := by
  rw [reference, gaussian_integral]

end Artform.Scores.NonabelianGravity.HistoryGaussian
