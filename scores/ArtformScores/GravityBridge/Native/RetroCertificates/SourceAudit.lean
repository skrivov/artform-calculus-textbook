import ArtformScores.GravityBridge.Native.RetroCertificates.SourceAuditStatements

/-! # Selected native sources do not certify the full inverse -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40 TTCross
omit [CharZero K] in
lemma old_three_source_not_complete_certificate (p m s : Fin 3 → K) :
    sourceOnlyReturn (threeConnection p m s) = fullHApply (threeConnection p m s) := by
  simp [sourceOnlyReturn, fullHApply, threeConnection, generic_partition_repeated]

omit [CharZero K] in
lemma actual_selected_adjoint_not_complete_certificate (p m s : Fin 3 → K) :
    sourceOnlyReturn (nativeSourceAdjoint (threeBlockFace p m s)) =
      fullHApply (nativeSourceAdjoint (threeBlockFace p m s)) := by
  rw [native_adjoint_three_blocks]
  exact old_three_source_not_complete_certificate _ _ _

omit [CharZero K] in
lemma lost_repeated_source (z : Fin 3 → K) (b : Fin 4) :
    sourceOnlyReturn (gRepeatedInput b z) = 0 := by
  have hD : gDistinct (gRepeatedInput b z) = 0 := by
    ext s i
    fin_cases s <;> fin_cases b <;> fin_cases i <;>
      simp [gDistinct, gRepeatedInput, gOriented, Retrospective.distinctIndices,
        Fin.succAbove, Fin.lt_def, wedge, basisVector, Fin.sum_univ_succ]
  ext mu a
  simp [sourceOnlyReturn, hD, gAssemble, gDistinctInput, gRepeatedInput, Fin.sum_univ_succ]

lemma source_only_passes_three_blocks_but_fails_full_inverse :
    (∀ p m s : Fin 3 → ℚ, sourceOnlyReturn (threeConnection p m s) =
      fullHApply (threeConnection p m s)) ∧
    fullBApply (sourceOnlyReturn (gRepeatedInput 1 (![1, 0, 0] : Fin 3 → ℚ))) ≠ 
      gRepeatedInput 1 ![1, 0, 0] := by
  refine ⟨old_three_source_not_complete_certificate, ?_⟩
  rw [lost_repeated_source]
  intro h
  have hx := congrFun (congrFun h 0) 0
  norm_num [fullBApply, gAssemble, gDistinct, gRepeated, gOriented, gDistinctInput, gRepeatedInput,
    Retrospective.distinctIndices, Fin.succAbove, Fin.lt_def, wedge, basisVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hx

/-- **GAC2:native-source-only-certificate-audit**
(selected native sources do not certify the full inverse). -/
@[ledger "GAC2:native-source-only-certificate-audit"]
theorem sourceAuditLaw : Statement.sourceAuditLaw := by
  intro K _ _
  exact ⟨old_three_source_not_complete_certificate,
    actual_selected_adjoint_not_complete_certificate,
    lost_repeated_source,
    source_only_passes_three_blocks_but_fails_full_inverse⟩

/-! ## Non-vacuity -/
example : sourceOnlyReturn (gRepeatedInput 1 (![1, 2, 3] : Fin 3 → ℚ)) = 0 :=
  lost_repeated_source _ _

end Artform.Scores.GravityBridge.Native.RetroCertificates
