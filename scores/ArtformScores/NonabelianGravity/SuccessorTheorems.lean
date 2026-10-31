import ArtformScores.NonabelianGravity.SuccessorStatements

/-! # Proofs and non-vacuity controls for all three successor questions -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
open Filter Topology NonlinearAmbient NonlinearIsotropic HistoryElimination QuantumComposition

/-- **NGB:native-full40-obstruction** (an actual source derivative, with all40 correctors). -/
@[ledger "NGB:native-full40-obstruction"]
theorem nativeFull40Obstruction : Statement.nativeFull40Obstruction :=
  ⟨force_binding, force_strict_critical, arbitrary_correction_limit, full40_no_repair,
    future_boundary_fixed,
    prepared_linear_match⟩

/-- **NGB:native-common-volume-schur** (Jacobian-normalized native references agree). -/
@[ledger "NGB:native-common-volume-schur"]
theorem nativeCommonVolumeSchur : Statement.nativeCommonVolumeSchur :=
  ⟨left_schur_solve, right_schur_solve, left_upper_product, right_lower_product,
    left_phase, right_phase, native_volume_left, native_volume_right,
    original_equations_retained, original_source_contact,
    native_common_volume_composition, native_opposite_orders,
    native_schur_admission leftCertificate, nonzero_contact_retained, nonzero_source_admitted⟩

/-- **NGB:native-long-history-obstruction** (the same obstruction after increasing history). -/
@[ledger "NGB:native-long-history-obstruction"]
theorem nativeLongHistoryObstruction : Statement.nativeLongHistoryObstruction :=
  ⟨NonlinearLongHistory.complete_linear_match, full_history_lapse_difference,
    full_history_force_binding, NonlinearLongHistory.coefficient_values,
    NonlinearLongCorrection.fixed_endpoints, NonlinearLongCorrection.every_owned_chart_admitted,
    NonlinearLongCorrection.full_force_limit,
    NonlinearLongCorrection.every_lapse_eventually_nonzero⟩

/-! ## Non-vacuity -/
example : Legendre.post 0 preparedMiddle - Legendre.pre preparedMiddle preparedFinal = 0 :=
  prepared_linear_match

example : ∀ᶠ e in 𝓝[≠] (0 : ℝ), Physical (correctedPrepared 0 e) ∧
    force (correctedPrepared 0 e) ≠ 0 := (full40_no_repair 0).2

example : (nativeSchurReference leftCertificate 0 0 quantumSource 1).isSome ∧
    sourceContact leftCertificate (restrict quantumSource) = 4 / 101 :=
  ⟨nonzero_source_admitted, nonzero_contact_retained⟩

example : NativeMatch 0 preparedFinal 0 NonlinearLongHistory.history ∧
    ∀ᶠ e in 𝓝[≠] (0 : ℝ), ∀ t : Fin 3, NonlinearLongCorrection.lapseForce 0 t e ≠ 0 :=
  ⟨NonlinearLongHistory.complete_linear_match,
    NonlinearLongCorrection.every_lapse_eventually_nonzero 0⟩

end Artform.Scores.NonabelianGravity
