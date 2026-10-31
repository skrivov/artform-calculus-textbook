import ArtformScores.NonabelianGravity.HistoryQuantumStatements

/-! # Source-bound reference theorem and concrete nonvacuity -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
open HistoryElimination

@[ledger "NGB:native-contour-reference"]
theorem nativeContourReference : Statement.nativeContourReference := by
  exact ⟨three_action_decomposition, three_stationary_action,
    fun c E r ℏ h => ⟨contour_integrable c E r ℏ h, reference_amplitude_formula c E r ℏ h⟩,
    rotation_determinant, permutation_normalization, native_reference_admission,
    reference_dimension, reference_positive_pivots, reference_negative_pivots,
    reference_phase_one, quantum_source_nonzero, quantum_source_contact,
    zero_reference_admitted, incompatible_reference_rejected⟩

example : (nativeReference sampleCertificate 0 0 0 1).isSome :=
  zero_reference_admitted 1 (by norm_num)

example : quantumSource ≠ 0 := by
  intro h
  have hq := quantum_source_nonzero
  rw [h] at hq
  norm_num at hq

end Artform.Scores.NonabelianGravity
