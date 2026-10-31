import ArtformScores.NonabelianGravity.QuantumSliceLeft
import ArtformScores.NonabelianGravity.QuantumSliceRight
import ArtformScores.NonabelianGravity.QuantumSliceBinding
import ArtformScores.NonabelianGravity.QuantumSliceAP
import ArtformScores.NonabelianGravity.QuantumSliceDQ
import ArtformScores.NonabelianGravity.QuantumSliceUpper
import ArtformScores.NonabelianGravity.QuantumSliceLower
import ArtformScores.NonabelianGravity.QuantumPhase

/-! # Opposite Schur references on exactly one native66-coordinate volume -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.QuantumComposition
open HistoryElimination

lemma left_pivots_nonzero (i : SliceIndex) : leftDiagonal i ≠ 0 := by
  rcases i with i | i <;> fin_cases i <;> decide +kernel
lemma right_pivots_nonzero (i : SliceIndex) : rightDiagonal i ≠ 0 := by
  rcases i with i | i <;> fin_cases i <;> decide +kernel

noncomputable def leftCertificate : Certificate nativeSlice :=
  certificateOfNonzero nativeSlice leftForward leftDiagonal
    (by rw [slice_binding]; exact left_congruence_data) left_pivots_nonzero
noncomputable def rightCertificate : Certificate nativeSlice :=
  certificateOfNonzero nativeSlice rightForward rightDiagonal
    (by rw [slice_binding]; exact right_congruence_data) right_pivots_nonzero

lemma left_phase : rotationPhase leftCertificate = 1 := by
  apply phase_of_counts <;> decide +kernel
lemma right_phase : rotationPhase rightCertificate = 1 := by
  apply phase_of_counts <;> decide +kernel

lemma native_common_volume_composition (E : ℚ) (r : SliceIndex → ℚ) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    volumeReference leftCertificate E r ℏ = volumeReference rightCertificate E r ℏ := by
  exact common_volume_composition leftCertificate rightCertificate left_pivots_nonzero
    right_pivots_nonzero (left_phase.trans right_phase.symm) E r ℏ hℏ

lemma native_volume_left :
    MeasureTheory.Measure.map
      (Matrix.toLin' (leftForward.map (algebraMap ℚ ℝ))) MeasureTheory.volume =
      ENNReal.ofReal ((realJacobian leftCertificate)⁻¹) • MeasureTheory.volume :=
  native_volume_transport leftCertificate

lemma native_volume_right :
    MeasureTheory.Measure.map
      (Matrix.toLin' (rightForward.map (algebraMap ℚ ℝ))) MeasureTheory.volume =
      ENNReal.ofReal ((realJacobian rightCertificate)⁻¹) • MeasureTheory.volume :=
  native_volume_transport rightCertificate

end Artform.Scores.NonabelianGravity.QuantumComposition
