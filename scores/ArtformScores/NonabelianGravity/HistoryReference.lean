import ArtformScores.NonabelianGravity.HistoryContourIntegral

/-! # Conditional native reference amplitudes with explicit source admission

Volume is Lebesgue in the fixed certificate coordinates, with all zero-pivot
coordinates fixed to zero. The complex diagonal rotation determinant is kept.
This is a declared reference prescription, not a selected physical measure.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
open HistoryGaussian MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Matrix ι ι ℚ} (c : Certificate H)

noncomputable def rotationPhase : ℂ := ∏ i : Active c, wick (activeDiagonal c i)

lemma rotation_determinant :
    (Matrix.diagonal (fun i : Active c => wick (activeDiagonal c i))).det = rotationPhase c :=
  Matrix.det_diagonal

noncomputable def referenceAmplitude (E : ℚ) (r : ι → ℚ) (ℏ : ℝ) : ℂ :=
  rotationPhase c * ∫ t : Active c → ℝ, Complex.exp (contourExponent c E r ℏ t)

lemma reference_amplitude_formula (E : ℚ) (r : ι → ℚ) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    referenceAmplitude c E r ℏ = rotationPhase c *
      Complex.exp (Complex.I * (stationary c E r : ℂ) / ℏ) *
        ((∏ i : Active c, Real.sqrt (Real.pi /
          (|activeDiagonal c i| / (2 * ℏ))) : ℝ) : ℂ) := by
  rw [referenceAmplitude, contour_integral c E r ℏ hℏ]
  ring

lemma permutation_normalization (ℏ : ℝ) (e : Active c ≃ Active c) :
    (∏ i : Active c, wick (activeDiagonal c (e i))) *
      ((∏ i : Active c, Real.sqrt (Real.pi /
        (|activeDiagonal c (e i)| / (2 * ℏ))) : ℝ) : ℂ) =
    rotationPhase c * ((∏ i : Active c, Real.sqrt (Real.pi /
        (|activeDiagonal c i| / (2 * ℏ))) : ℝ) : ℂ) := by
  rw [e.prod_comp (fun i => wick (activeDiagonal c i)),
    e.prod_comp (fun i => Real.sqrt (Real.pi / (|activeDiagonal c i| / (2 * ℏ))))]
  rfl

open Legendre in
noncomputable def nativeReference (c : Certificate (historyMatrix 2))
    (x z : Point ℚ) (j : Vector 2) (ℏ : ℝ) : Option ℂ := by
  classical
  exact if 0 < ℏ ∧ Compatible c (sourceResidual x z j) then
    some (referenceAmplitude c (endpointAction x z) (sourceResidual x z j) ℏ) else none

open Legendre in
lemma native_reference_admission (c : Certificate (historyMatrix 2))
    (x z : Point ℚ) (j : Vector 2) (ℏ : ℝ) :
    (nativeReference c x z j ℏ).isSome ↔ 0 < ℏ ∧ ∃ y, NativeMatch x z j y := by
  classical
  rw [native_source_iff c]
  simp [nativeReference]

end Artform.Scores.NonabelianGravity.HistoryElimination
