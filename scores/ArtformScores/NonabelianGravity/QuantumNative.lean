import ArtformScores.NonabelianGravity.QuantumSchur
import ArtformScores.NonabelianGravity.QuantumCarrier

/-! # Both contour orders retain every original source equation and affine contact -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.QuantumComposition
open HistoryElimination Legendre

lemma reduced_solution_unique (c : Certificate nativeSlice)
    (hd : ∀ i, c.diagonal i ≠ 0) (r y : Reduced) (hy : nativeSlice.mulVec y = r) :
    y = solution c r 0 := by
  have h := solution_complete c y r hy
  have he : solution c r (c.backward.mulVec y) = solution c r 0 := by
    unfold solution
    congr 1
    funext i
    simp only [hd i, ite_false]
  exact h.trans he

lemma original_equations_retained (r : Whole)
    (hr : Compatible sampleCertificate r) :
    (historyMatrix 2).mulVec (embed (solution leftCertificate (restrict r) 0)) = r := by
  obtain ⟨y, hy, hys⟩ := admitted_slice_exists r ((solvable_iff sampleCertificate r).mpr hr)
  rw [← reduced_solution_unique leftCertificate left_pivots_nonzero (restrict r) y hys]
  exact hy

lemma dot_embed (r : Whole) (y : Reduced) : dotProduct r (embed y) = dotProduct (restrict r) y := by
  simp only [dotProduct, embed, restrict]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_ite, mul_zero]
  simp

lemma embedded_quadratic (r : Whole) (y : Reduced) :
    quadraticAction (H := historyMatrix 2) r (embed y) =
      quadraticAction (H := nativeSlice) (restrict r) y := by
  rw [quadraticAction, quadraticAction, dot_embed]
  have hq : dotProduct (embed y) ((historyMatrix 2).mulVec (embed y)) =
      dotProduct y (nativeSlice.mulVec y) := by
    rw [dotProduct_comm, dot_embed, ← slice_equation, dotProduct_comm]
  rw [hq]

lemma original_source_contact (r : Whole) (hr : Compatible sampleCertificate r) :
    sourceContact sampleCertificate r = sourceContact leftCertificate (restrict r) := by
  let y := solution leftCertificate (restrict r) 0
  have hE := original_equations_retained r hr
  have hcomplete := solution_complete sampleCertificate (embed y) r hE
  have hfull := stationary_quadratic sampleCertificate r
    (sampleCertificate.backward.mulVec (embed y)) hr
  rw [← hcomplete, embedded_quadratic] at hfull
  have hsmall := stationary_quadratic leftCertificate (restrict r) 0
    (fun i hi => False.elim (left_pivots_nonzero i hi))
  change quadraticAction (restrict r) y = _ at hsmall
  linarith

noncomputable def nativeSchurReference (c : Certificate nativeSlice)
    (x z : Point ℚ) (j : Vector 2) (ℏ : ℝ) : Option ℂ := by
  classical
  exact if 0 < ℏ ∧ Compatible sampleCertificate (sourceResidual x z j) then
    some (volumeReference c (endpointAction x z) (restrict (sourceResidual x z j)) ℏ)
  else none

lemma native_schur_admission (c : Certificate nativeSlice)
    (x z : Point ℚ) (j : Vector 2) (ℏ : ℝ) :
    (nativeSchurReference c x z j ℏ).isSome ↔ 0 < ℏ ∧ ∃ y, NativeMatch x z j y := by
  classical
  rw [native_source_iff sampleCertificate]
  simp [nativeSchurReference]

lemma native_opposite_orders (x z : Point ℚ) (j : Vector 2) (ℏ : ℝ) :
    nativeSchurReference leftCertificate x z j ℏ =
      nativeSchurReference rightCertificate x z j ℏ := by
  classical
  unfold nativeSchurReference
  split_ifs with h
  · rw [native_common_volume_composition _ _ ℏ h.1]
  · rfl

lemma nonzero_contact_retained :
    sourceContact leftCertificate (restrict quantumSource) = 4 / 101 := by
  rw [← original_source_contact quantumSource (quantum_source_compatible sampleCertificate)]
  exact quantum_source_contact sampleCertificate

lemma nonzero_source_admitted :
    (nativeSchurReference leftCertificate 0 0 quantumSource 1).isSome := by
  rw [native_schur_admission]
  refine ⟨by norm_num, ?_⟩
  apply (native_source_iff sampleCertificate 0 0 quantumSource).mpr
  have he : sourceResidual (0 : Point ℚ) 0 quantumSource = quantumSource := by
    funext k
    simp [sourceResidual]
  rw [he]
  exact quantum_source_compatible sampleCertificate

end Artform.Scores.NonabelianGravity.QuantumComposition
