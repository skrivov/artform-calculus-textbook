import ArtformScores.NonabelianGravity.HistoryReferenceSample
import ArtformScores.Meta.Ledger

/-! # Conditional native contour reference, explicit measure and admission -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Statement
open Legendre HistoryElimination HistoryGaussian MeasureTheory

/-- **NGB:native-contour-reference** (fixed-certificate Lebesgue reference only). -/
@[ledger "NGB:native-contour-reference"]
def nativeContourReference : Prop :=
  (∀ (x z : Point ℚ) (j y : Vector 2), threeAction x z j y = endpointAction x z +
    quadraticAction (H := historyMatrix 2) (sourceResidual x z j) y) ∧
  (∀ (c : Certificate (historyMatrix 2)) (x z : Point ℚ) (j free : Vector 2),
    Compatible c (sourceResidual x z j) →
      threeAction x z j (solution c (sourceResidual x z j) free) =
        endpointAction x z - (1 / 2 : ℚ) * sourceContact c (sourceResidual x z j)) ∧
  (∀ (c : Certificate (historyMatrix 2)) (E : ℚ) (r : Vector 2) (ℏ : ℝ), 0 < ℏ →
    Integrable (fun t : Active c → ℝ => Complex.exp (contourExponent c E r ℏ t)) ∧
    referenceAmplitude c E r ℏ = rotationPhase c *
      Complex.exp (Complex.I * (stationary c E r : ℂ) / ℏ) *
        ((∏ i : Active c, Real.sqrt (Real.pi /
          (|activeDiagonal c i| / (2 * ℏ))) : ℝ) : ℂ)) ∧
  (∀ c : Certificate (historyMatrix 2),
    (Matrix.diagonal (fun i : Active c => wick (activeDiagonal c i))).det = rotationPhase c) ∧
  (∀ (c : Certificate (historyMatrix 2)) (ℏ : ℝ) (e : Active c ≃ Active c),
    (∏ i : Active c, wick (activeDiagonal c (e i))) *
      ((∏ i : Active c, Real.sqrt (Real.pi /
        (|activeDiagonal c (e i)| / (2 * ℏ))) : ℝ) : ℂ) =
    rotationPhase c * ((∏ i : Active c, Real.sqrt (Real.pi /
        (|activeDiagonal c i| / (2 * ℏ))) : ℝ) : ℂ)) ∧
  (∀ (c : Certificate (historyMatrix 2)) (x z : Point ℚ) (j : Vector 2) (ℏ : ℝ),
    (nativeReference c x z j ℏ).isSome ↔ 0 < ℏ ∧ ∃ y, NativeMatch x z j y) ∧
  Fintype.card (Active sampleCertificate) = 66 ∧
  Fintype.card {i : Index 2 // 0 < sampleDiagonal i} = 37 ∧
  Fintype.card {i : Index 2 // sampleDiagonal i < 0} = 29 ∧
  rotationPhase sampleCertificate = 1 ∧
  quantumSource (0, 25) = 4 / 101 ∧
  (∀ c : Certificate (historyMatrix 2), sourceContact c quantumSource = 4 / 101) ∧
  (∀ ℏ : ℝ, 0 < ℏ → (nativeReference sampleCertificate 0 0 0 ℏ).isSome) ∧
  (∀ ℏ : ℝ, nativeReference sampleCertificate 0 0 incompatibleSource ℏ = none)

end Artform.Scores.NonabelianGravity.Statement
