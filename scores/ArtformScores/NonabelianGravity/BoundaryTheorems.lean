import ArtformScores.NonabelianGravity.BoundaryStatements

/-! # Checked native boundary continuation and non-vacuity -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
open Legendre BoundarySymbol BoundaryHistory BoundaryQuantum
open Artform.Scores.GravityBridge.Native.Full40

@[ledger "NGB:native-boundary-conditioning"]
theorem nativeBoundaryConditioning : Statement.nativeBoundaryConditioning :=
  ⟨native_mixed_formula, circle_mixed_formula, rotation_norm, rotation_frequency_irrational,
    rotation_dense, rotation_power_ne_minus_one, left_witness, column22, column_norm,
    fun n v h => ⟨kernel_coordinate n v h, boost_orthogonal_to_kernel n v h⟩,
    no_uniform_coordinate_estimate⟩

@[ledger "NGB:native-history-source-guard"]
theorem nativeHistorySourceGuard : Statement.nativeHistorySourceGuard :=
  ⟨fun w => ⟨first_binding w, second_binding w, first_null w, second_null w,
      incoming_zero w, outgoing_zero w, endpoint_binding w⟩,
    source_compatibility, source16_active, source16_rejected, zero_three_cell⟩

@[ledger "NGB:native-quantum-kernel-tests"]
theorem nativeQuantumKernelTests : Statement.nativeQuantumKernelTests :=
  ⟨output_nonzero, action_output_flat, negative_ray, phase_output_flat⟩

/-! ## Non-vacuity -/

example : mixedApply (rotationValue ^ (0 : ℤ)) boostUnit 10 = -1 / 2 := by
  norm_num [mixedApply, boostUnit]

example : ThreeCellMatch 0 0 0 0 0 0 := zero_three_cell

example : activeProjector.mulVec source16 = source16 := source16_active

example : cutAction negativeDirection 0 < 0 := by
  have h := negative_ray 1
  norm_num at h
  rw [h]
  norm_num

example : outputDirection ≠ 0 := output_nonzero

end Artform.Scores.NonabelianGravity
