import ArtformScores.GravityBridge.Native.NativeCurrent.ProcessingStatements

/-! # Complete pulled-current change and norm bound -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent

variable {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma bilinear_pullback_norm (B : H →L[ℝ] H →L[ℝ] ℝ) (E F : Y →L[ℝ] H) :
    ‖B.bilinearComp E F‖ ≤ ‖B‖ * ‖E‖ * ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro x y
  change ‖B (E x) (F y)‖ ≤ ‖B‖ * ‖E‖ * ‖F‖ * ‖x‖ * ‖y‖
  calc
    _ ≤ ‖B‖ * ‖E x‖ * ‖F y‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * (‖E‖ * ‖x‖) * (‖F‖ * ‖y‖) := by
      gcongr
      · exact E.le_opNorm x
      · exact F.le_opNorm y
    _ = _ := by ring

lemma complete_current_change (B : H →L[ℝ] H →L[ℝ] ℝ) (E D : Y →L[ℝ] H) :
    pulledCurrent B (E + D) - pulledCurrent B E =
      B.bilinearComp E D + B.bilinearComp D E + B.bilinearComp D D := by
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simp [pulledCurrent, map_add]
  ring

lemma complete_current_change_norm (B : H →L[ℝ] H →L[ℝ] ℝ) (E D : Y →L[ℝ] H) :
    ‖pulledCurrent B (E + D) - pulledCurrent B E‖ ≤ ‖B‖ * (2 * ‖E‖ * ‖D‖ + ‖D‖ ^ 2) := by
  rw [complete_current_change]
  have htri := norm_add_le
    (B.bilinearComp E D + B.bilinearComp D E : Y →L[ℝ] Y →L[ℝ] ℝ)
    (B.bilinearComp D D : Y →L[ℝ] Y →L[ℝ] ℝ)
  have htri₂ := norm_add_le
    (B.bilinearComp E D : Y →L[ℝ] Y →L[ℝ] ℝ)
    (B.bilinearComp D E : Y →L[ℝ] Y →L[ℝ] ℝ)
  calc
    _ ≤ ‖B.bilinearComp E D + B.bilinearComp D E‖ + ‖B.bilinearComp D D‖ := htri
    _ ≤ (‖B.bilinearComp E D‖ + ‖B.bilinearComp D E‖) + ‖B.bilinearComp D D‖ := by
      linarith only [htri₂]
    _ ≤ (‖B‖ * ‖E‖ * ‖D‖ + ‖B‖ * ‖D‖ * ‖E‖) + ‖B‖ * ‖D‖ * ‖D‖ := by
      gcongr <;> exact bilinear_pullback_norm _ _ _
    _ = _ := by ring

lemma radical_change_preserves_current (B : H →L[ℝ] H →L[ℝ] ℝ) (E D : Y →L[ℝ] H)
    (hl : ∀ x z, B (D x) z = 0) (hr : ∀ x z, B z (D x) = 0) :
    pulledCurrent B (E + D) = pulledCurrent B E := by
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  change B (E x + D x) (E y + D y) = B (E x) (E y)
  simp [map_add, hl, hr]

/-- **GAC2:complete-current-processing-defect**
(complete pulled-current change and norm bound). -/
@[ledger "GAC2:complete-current-processing-defect"]
theorem processingLaw : Statement.processingLaw := by
  intro H Y _ _ _ _
  exact ⟨bilinear_pullback_norm,
    complete_current_change,
    complete_current_change_norm,
    radical_change_preserves_current⟩

/-! ## Non-vacuity -/

example : (pulledCurrent (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.id ℝ ℝ + ContinuousLinearMap.id ℝ ℝ)-
    pulledCurrent (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)) 1 1 = 3 := by
  norm_num [pulledCurrent]

end Artform.Scores.GravityBridge.Native.NativeCurrent
