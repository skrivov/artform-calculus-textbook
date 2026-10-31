import ArtformScores.NonabelianGravity.NonlinearFull40
import ArtformScores.NonabelianGravity.NonlinearLongCorrection
import ArtformScores.NonabelianGravity.QuantumNative
import ArtformScores.Meta.Ledger

/-! # Three source-bound successor questions, with explicit domains -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Statement
open Filter Topology Asymptotics NonlinearAmbient NonlinearIsotropic
open HistoryElimination QuantumComposition
open scoped Matrix.Norms.Elementwise

/-- **NGB:native-full40-obstruction** (all owned native second-order coefficients). -/
@[ledger "NGB:native-full40-obstruction"]
def nativeFull40Obstruction : Prop :=
  (∀ q : Env, Regular q → force q = forceFormula q) ∧
  HasStrictFDerivAt force (0 : Env →L[ℝ] ℝ) flat ∧
  (∀ f b g : ℝ, ∀ u : ℝ → Env,
    Tendsto u (𝓝[≠] 0) (𝓝 flat) →
    (fun e => u e - rateCurve f b g e) =O[𝓝[≠] 0] (fun e => e ^ 2) →
    Tendsto (fun e : ℝ => force (u e) / e ^ 2) (𝓝[≠] 0)
      (𝓝 (3 * ((100 / 101) * b ^ 2 + (1 / 101) * (g - f) ^ 2)))) ∧
  (∀ w : OwnedCorrector,
    Tendsto (fun e : ℝ => force (correctedPrepared w e) / e ^ 2) (𝓝[≠] 0)
      (𝓝 (40501 / 53868)) ∧
    ∀ᶠ e in 𝓝[≠] (0 : ℝ), Physical (correctedPrepared w e) ∧
      force (correctedPrepared w e) ≠ 0) ∧
  (∀ w : OwnedCorrector, ∀ e : ℝ,
    (correctedPrepared w e).1.2 = frame 1 (1 + e)) ∧
  (Legendre.post 0 preparedMiddle - Legendre.pre preparedMiddle preparedFinal = 0)

/-- **NGB:native-common-volume-schur** (two specified actual contour references). -/
@[ledger "NGB:native-common-volume-schur"]
def nativeCommonVolumeSchur : Prop :=
  leftA * leftP = crossB ∧ rightD * rightQ = crossB.transpose ∧
  leftUpper = -(leftP * leftSchurBasis) ∧ rightLower = -(rightQ * rightSchurBasis) ∧
  rotationPhase leftCertificate = 1 ∧ rotationPhase rightCertificate = 1 ∧
  (MeasureTheory.Measure.map (Matrix.toLin' (leftForward.map (algebraMap ℚ ℝ)))
    MeasureTheory.volume = ENNReal.ofReal ((realJacobian leftCertificate)⁻¹) •
      MeasureTheory.volume) ∧
  (MeasureTheory.Measure.map (Matrix.toLin' (rightForward.map (algebraMap ℚ ℝ)))
    MeasureTheory.volume = ENNReal.ofReal ((realJacobian rightCertificate)⁻¹) •
      MeasureTheory.volume) ∧
  (∀ r : Whole, Compatible sampleCertificate r →
    (historyMatrix 2).mulVec (embed (solution leftCertificate (restrict r) 0)) = r) ∧
  (∀ r : Whole, Compatible sampleCertificate r →
    sourceContact sampleCertificate r = sourceContact leftCertificate (restrict r)) ∧
  (∀ E : ℚ, ∀ r : Reduced, ∀ ℏ : ℝ, 0 < ℏ →
    volumeReference leftCertificate E r ℏ = volumeReference rightCertificate E r ℏ) ∧
  (∀ x z : Legendre.Point ℚ, ∀ j : Vector 2, ∀ ℏ : ℝ,
    nativeSchurReference leftCertificate x z j ℏ = nativeSchurReference rightCertificate x z j ℏ) ∧
  (∀ x z : Legendre.Point ℚ, ∀ j : Vector 2, ∀ ℏ : ℝ,
    (nativeSchurReference leftCertificate x z j ℏ).isSome ↔
      0 < ℏ ∧ ∃ y, NativeMatch x z j y) ∧
  sourceContact leftCertificate (restrict quantumSource) = 4 / 101 ∧
  (nativeSchurReference leftCertificate 0 0 quantumSource 1).isSome

/-- **NGB:native-long-history-obstruction** (one corrected120-coordinate history). -/
@[ledger "NGB:native-long-history-obstruction"]
def nativeLongHistoryObstruction : Prop :=
  NativeMatch 0 preparedFinal 0 NonlinearLongHistory.history ∧
  (∀ E : ℕ → Mat, ∀ U : ℕ → Fin 4 → Mat, ∀ n : Fin 4, ∀ s : ℝ,
    fourCellAction (bumpAt E n.val s) U - fourCellAction E U =
      action (cellEnv (fun k => E (n.val + k)) (fun k => U (n.val + k)) + s • lapseDirection) -
        action (cellEnv (fun k => E (n.val + k)) (fun k => U (n.val + k)))) ∧
  (∀ E : ℕ → Mat, ∀ U : ℕ → Fin 4 → Mat, ∀ n : Fin 4,
    Regular (cellEnv (fun k => E (n.val + k)) (fun k => U (n.val + k))) →
    HasDerivAt (fun s => fourCellAction (bumpAt E n.val s) U)
      (force (cellEnv (fun k => E (n.val + k)) (fun k => U (n.val + k)))) 0) ∧
  NonlinearLongHistory.coefficient =
    ![1263813303 / 6856502416, 4414503 / 6856502416, 1337735703 / 6856502416] ∧
  (∀ w : NonlinearLongCorrection.Corrections, ∀ e : ℝ,
    NonlinearLongCorrection.E w e 0 = 1 ∧ NonlinearLongCorrection.E w e 4 = frame 1 (1 + e)) ∧
  (∀ w : NonlinearLongCorrection.Corrections,
    ∀ᶠ e in 𝓝 (0 : ℝ), ∀ t : Fin 3,
      Physical (cellEnv (fun k => NonlinearLongCorrection.E w e
        ((NonlinearLongCorrection.site t).val + k))
        (fun k => NonlinearLongCorrection.U w e ((NonlinearLongCorrection.site t).val + k)))) ∧
  (∀ w : NonlinearLongCorrection.Corrections, ∀ t : Fin 3,
    Tendsto (fun e : ℝ => NonlinearLongCorrection.lapseForce w t e / e ^ 2)
      (𝓝[≠] 0) (𝓝 (NonlinearLongHistory.coefficient t : ℝ))) ∧
  (∀ w : NonlinearLongCorrection.Corrections,
    ∀ᶠ e in 𝓝[≠] (0 : ℝ), ∀ t : Fin 3, NonlinearLongCorrection.lapseForce w t e ≠ 0)

end Artform.Scores.NonabelianGravity.Statement
