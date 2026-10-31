import ArtformScores.GravityBridge.Native.R7Blocks.FeedbackStatements

/-! # Complete Riccati recentering and quadratic feedback -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma full_riccati_recenter (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K D : Y →L[ℝ] Z) :
    blockDefect A11 A12 A21 A22 (K + D) =
      blockDefect A11 A12 A21 A22 K + linearizedRiccati A11 A12 A22 K D-
        (D.comp A12).comp D := by
  apply ContinuousLinearMap.ext
  intro y
  simp only [blockDefect, ownDataAction, linearizedRiccati, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, map_add]
  abel

lemma feedback_remainder_exact (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K D : Y →L[ℝ] Z) :
    blockDefect A11 A12 A21 A22 (K + D) - blockDefect A11 A12 A21 A22 K-
      linearizedRiccati A11 A12 A22 K D = -(D.comp A12).comp D := by
  rw [full_riccati_recenter]
  abel

lemma feedback_remainder_norm (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K D : Y →L[ℝ] Z) :
    ‖blockDefect A11 A12 A21 A22 (K + D) - blockDefect A11 A12 A21 A22 K-
      linearizedRiccati A11 A12 A22 K D‖ ≤ ‖A12‖ * ‖D‖ ^ 2 := by
  rw [feedback_remainder_exact, norm_neg]
  calc
    _ ≤ ‖D.comp A12‖ * ‖D‖ := (D.comp A12).opNorm_comp_le D
    _ ≤ (‖D‖ * ‖A12‖) * ‖D‖ :=
      mul_le_mul_of_nonneg_right (D.opNorm_comp_le A12) (norm_nonneg _)
    _ = ‖A12‖ * ‖D‖ ^ 2 := by ring

/-- **GAC2:full-riccati-feedback**
(complete riccati recentering and quadratic feedback). -/
@[ledger "GAC2:full-riccati-feedback"]
theorem feedbackLaw : Statement.feedbackLaw := by
  intro Y Z _ _ _ _
  exact ⟨full_riccati_recenter,
    feedback_remainder_exact,
    feedback_remainder_norm⟩

/-! ## Non-vacuity -/

example :
    (blockDefect 0 (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) 0
      (ContinuousLinearMap.id ℝ ℝ + ContinuousLinearMap.id ℝ ℝ)) 1 = -3 ∧
    (linearizedRiccati 0 (ContinuousLinearMap.id ℝ ℝ) 0
      (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)) 1 = -2 := by
  norm_num [blockDefect, ownDataAction, linearizedRiccati]

end Artform.Scores.GravityBridge.Native.R7Blocks
