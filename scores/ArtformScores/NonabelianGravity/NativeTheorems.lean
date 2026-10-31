import ArtformScores.NonabelianGravity.NativeStatements

/-! # A complete native-force obstruction for the conditional ansatz -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
open Artform.Scores.GravityBridge.Native.Full40 NativeRotation

/-- **NGB:native-rotation-import-test** (all40 rows, fixed halo and zero source). -/
@[ledger "NGB:native-rotation-import-test"]
theorem nativeRotationImportTest : Statement.nativeRotationImportTest :=
  ⟨integer_density_zero,
    fun u v => ⟨halo_density u v, density_binding u v, owned_action_binding u v⟩,
    fun j c => ⟨complete_columns j c, actual_columns j c⟩,
    fun v c => ⟨actual_rows v c, owned_row_binding v c⟩,
    trace_residual, traceless_residual, owned_force_zero_iff⟩

/-! ## Non-vacuity -/
example : (basis 0 0).1 = 0 ∧ (basis 0 0).2 1 3 = 1 ∧
    (basis 0 1).2 = 0 := by decide +kernel
example : fullForce step (1 / 101) (basis 0) (0, Sum.inr (1, 3)) = 4 / 101 ∧
    fullForce step (1 / 101) (basis 0) (0, Sum.inr (2, 4)) = -99 / 101 ∧
    fullForce step (1 / 101) (basis 0) (0, Sum.inr (3, 5)) = -99 / 101 := by
  simp only [actual_columns]
  decide +kernel
example : ∀ c, fullForce step (1 / 101) (trial 0) (0, c) = 0 :=
  (owned_force_zero_iff 0).mpr rfl
end Artform.Scores.NonabelianGravity
