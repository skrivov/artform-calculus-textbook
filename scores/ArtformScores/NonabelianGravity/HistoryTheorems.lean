import ArtformScores.NonabelianGravity.HistoryStatements

/-! # Complete history theorem registration -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
open HistoryElimination

@[ledger "NGB:native-complete-history"]
theorem nativeCompleteHistory : Statement.nativeCompleteHistory := by
  exact ⟨native_certificate_exists, fun _ => native_matching_iff,
    fun _ => native_source_iff, fun _ => native_solution_valid,
    fun _ => native_solution_complete, sample_left, sample_right,
    sampleCertificate.congruence, sample_pivots, zero_history, incompatible_rejected⟩

end Artform.Scores.NonabelianGravity
