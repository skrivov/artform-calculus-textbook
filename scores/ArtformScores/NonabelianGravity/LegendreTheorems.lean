import ArtformScores.NonabelianGravity.LegendreStatements

/-! # Source-bound native relations and their exact two-cell obstruction -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
open Legendre

@[ledger "NGB:native-legendre-score"]
theorem nativeLegendreScore : Statement.nativeLegendreScore :=
  ⟨fun u v => ⟨source_matrix u v, linear_cell_formula u v⟩,
    real_directional_derivative, mixed_rank, relation_factorization,
    unit_nonzero, admitted_unit⟩

@[ledger "NGB:native-boundary-composition"]
theorem nativeBoundaryComposition : Statement.nativeBoundaryComposition :=
  ⟨middle_inverse_right, middle_inverse_left, inverse_symmetric, middle_rank,
    matching_solution, stationary_action, composed_binding, mixed_rank, composed_rank,
    source_contact_witness, zero_matching, inactive_source_rejected,
    admitted_unit, unit_nonextension⟩

/-! ## Nonvacuity and controls -/
example : unit25 ≠ 0 := unit_nonzero
example : NativeRelation ((0 : Point ℚ), flatMomentum) (unit25, flatMomentum) := admitted_unit
example : ¬ ∃ b : Phase ℚ, NativeRelation (unit25, flatMomentum) b := unit_nonextension
example : post (0 : Point ℚ) 0 - pre 0 0 = 0 := zero_matching
example : effectiveAction 0 0 unit25 ≠ 0 := by rw [source_contact_witness]; norm_num

end Artform.Scores.NonabelianGravity
