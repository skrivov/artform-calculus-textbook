import ArtformScores.NonabelianGravity.HistoryComplex
import ArtformScores.NonabelianGravity.HistoryThreeAction

/-! # A declared complement and rotated contour for a certified singular form -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
open HistoryGaussian MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Matrix ι ι ℚ} (c : Certificate H)

abbrev Active := {i : ι // c.diagonal i ≠ 0}

noncomputable def activeDiagonal : Active c → ℝ := fun i => (c.diagonal i : ℝ)

lemma active_diagonal_ne (i : Active c) : activeDiagonal c i ≠ 0 := by
  change (c.diagonal i : ℝ) ≠ 0
  exact_mod_cast i.property

noncomputable def embed (w : Active c → ℂ) : ι → ℂ :=
  fun i => if hi : c.diagonal i = 0 then 0 else w ⟨i, hi⟩

lemma sum_active (f : Active c → ℂ) :
    (∑ i : ι, if hi : c.diagonal i = 0 then 0 else f ⟨i, hi⟩) = ∑ i, f i := by
  let g : ι → ℂ := fun i => if hi : c.diagonal i = 0 then 0 else f ⟨i, hi⟩
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i => c.diagonal i = 0) g
  have hp : (∑ i : {i : ι // c.diagonal i = 0}, g i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [g, i.property]
  have hn : (∑ i : Active c, g i) = ∑ i : Active c, f i := by
    apply Finset.sum_congr rfl
    intro i _
    simp [g, i.property]
  rw [hp, hn, zero_add] at hs
  exact hs.symm

lemma restricted_diagonal_action (r : ι → ℚ) (w : Active c → ℂ) :
    complexAction (H := H) (fun i => (r i : ℂ))
      ((complexMatrix c.forward).mulVec (embed c w)) =
    ∑ i : Active c, ((c.diagonal i : ℂ) / 2 * w i ^ 2 -
      (transformedSource c r i : ℂ) * w i) := by
  rw [complex_action_diagonal, complex_source]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ i : ι, if hi : c.diagonal i = 0 then 0 else
        (c.diagonal i : ℂ) / 2 * w ⟨i, hi⟩ ^ 2 -
          (transformedSource c r i : ℂ) * w ⟨i, hi⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c.diagonal i = 0 <;> simp [embed, hi]
      ring
    _ = _ := sum_active c (fun i => (c.diagonal i : ℂ) / 2 * w i ^ 2 -
      (transformedSource c r i : ℂ) * w i)

noncomputable def contourCoordinates (r : ι → ℚ) (t : Active c → ℝ) : Active c → ℂ :=
  fun i => (transformedSource c r i : ℂ) / (c.diagonal i : ℂ) +
    wick (activeDiagonal c i) * (t i : ℂ)

noncomputable def contour (r : ι → ℚ) (t : Active c → ℝ) : ι → ℂ :=
  (complexMatrix c.forward).mulVec (embed c (contourCoordinates c r t))

lemma contour_coordinate_completion (r : ι → ℚ) (ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (t : Active c → ℝ) (i : Active c) :
    Complex.I * ((c.diagonal i : ℂ) / 2 * contourCoordinates c r t i ^ 2 -
      (transformedSource c r i : ℂ) * contourCoordinates c r t i) / ℏ =
    -Complex.I * (transformedSource c r i : ℂ) ^ 2 /
      (2 * (c.diagonal i : ℂ) * ℏ) -
    ((|activeDiagonal c i| / (2 * ℏ) : ℝ) : ℂ) * (t i : ℂ) ^ 2 := by
  simpa only [contourCoordinates, activeDiagonal, Complex.ofReal_ratCast] using
    wick_completion (activeDiagonal c i) (transformedSource c r i : ℝ) (t i) ℏ
      (active_diagonal_ne c i) hℏ

lemma source_contact_active (r : ι → ℚ) :
    (sourceContact c r : ℂ) =
      ∑ i : Active c, (transformedSource c r i : ℂ) ^ 2 / (c.diagonal i : ℂ) := by
  simp only [sourceContact, Rat.cast_sum, Rat.cast_div, Rat.cast_pow]
  calc
    _ = ∑ i : ι, if hi : c.diagonal i = 0 then 0 else
        (transformedSource c r i : ℂ) ^ 2 / (c.diagonal i : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c.diagonal i = 0 <;> simp [hi]
    _ = _ := sum_active c (fun i =>
      (transformedSource c r i : ℂ) ^ 2 / (c.diagonal i : ℂ))

end Artform.Scores.NonabelianGravity.HistoryElimination
