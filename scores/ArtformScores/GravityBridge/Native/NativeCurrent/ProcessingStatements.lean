import ArtformScores.GravityBridge.Native.NativeCurrent.ProcessingDefs

/-! # Complete pulled-current change and norm bound -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent.Statement

/-- **GAC2:complete-current-processing-defect**
(complete pulled-current change and norm bound). -/
@[ledger "GAC2:complete-current-processing-defect"]
def processingLaw : Prop :=
  ∀ (H Y : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
    (∀ (B : H →L[ℝ] H →L[ℝ] ℝ) (E F : Y →L[ℝ] H),
    ‖B.bilinearComp E F‖ ≤ ‖B‖ * ‖E‖ * ‖F‖) ∧
    (∀ (B : H →L[ℝ] H →L[ℝ] ℝ) (E D : Y →L[ℝ] H),
    pulledCurrent B (E + D) - pulledCurrent B E =
      B.bilinearComp E D + B.bilinearComp D E + B.bilinearComp D D) ∧
    (∀ (B : H →L[ℝ] H →L[ℝ] ℝ) (E D : Y →L[ℝ] H),
    ‖pulledCurrent B (E + D) - pulledCurrent B E‖ ≤ ‖B‖ * (2 * ‖E‖ * ‖D‖ + ‖D‖ ^ 2)) ∧
    (∀ (B : H →L[ℝ] H →L[ℝ] ℝ) (E D : Y →L[ℝ] H)
    (_hl : ∀ x z, B (D x) z = 0) (_hr : ∀ x z, B z (D x) = 0),
    pulledCurrent B (E + D) = pulledCurrent B E)

end Artform.Scores.GravityBridge.Native.NativeCurrent.Statement
