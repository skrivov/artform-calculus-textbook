import ArtformScores.GravityBridge.GaugeVolumeDefs

/-! # Unfixed Gaussian gauge volume and regulator dependence -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:gaussian-gauge-volume** (unfixed gaussian gauge volume and regulator dependence). -/
@[ledger "GAC:gaussian-gauge-volume"]
def gaugeVolumeLaw : Prop :=
  (¬ MeasureTheory.Integrable (gaugeGaussian 0)) ∧
  (MeasureTheory.Integrable (fun q : ℝ => gaugeGaussian 0 (q, 0)) ∧
    (∫ q : ℝ, gaugeGaussian 0 (q, 0)) = Real.sqrt Real.pi) ∧
  (∀ epsilon : ℝ, 0 < epsilon →
    MeasureTheory.Integrable (gaugeGaussian epsilon) ∧
    (∫ x : ℝ × ℝ, gaugeGaussian epsilon x) =
      Real.sqrt Real.pi * Real.sqrt (Real.pi / epsilon)) ∧
  ((∫ x : ℝ × ℝ, gaugeGaussian 1 x) = Real.pi ∧
    (∫ x : ℝ × ℝ, gaugeGaussian 4 x) = Real.pi / 2 ∧
    (∫ x : ℝ × ℝ, gaugeGaussian 1 x) ≠ (∫ x : ℝ × ℝ, gaugeGaussian 4 x))

end Artform.Scores.GravityBridge.Statement
