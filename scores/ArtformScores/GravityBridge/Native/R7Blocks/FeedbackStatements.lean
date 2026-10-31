import ArtformScores.GravityBridge.Native.R7Blocks.FeedbackDefs

/-! # Complete Riccati recentering and quadratic feedback -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks.Statement


/-- **GAC2:full-riccati-feedback**
(complete riccati recentering and quadratic feedback). -/
@[ledger "GAC2:full-riccati-feedback"]
def feedbackLaw : Prop :=
  ∀ (Y Z : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z],
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K D : Y →L[ℝ] Z),
    blockDefect A11 A12 A21 A22 (K + D) =
      blockDefect A11 A12 A21 A22 K + linearizedRiccati A11 A12 A22 K D-
        (D.comp A12).comp D) ∧
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K D : Y →L[ℝ] Z),
    blockDefect A11 A12 A21 A22 (K + D) - blockDefect A11 A12 A21 A22 K-
      linearizedRiccati A11 A12 A22 K D = -(D.comp A12).comp D) ∧
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K D : Y →L[ℝ] Z),
    ‖blockDefect A11 A12 A21 A22 (K + D) - blockDefect A11 A12 A21 A22 K-
      linearizedRiccati A11 A12 A22 K D‖ ≤ ‖A12‖ * ‖D‖ ^ 2)

end Artform.Scores.GravityBridge.Native.R7Blocks.Statement
