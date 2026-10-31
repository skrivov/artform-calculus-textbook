import ArtformScores.GravityBridge.MetricFrameDefs
/-! # Metric jets and independent frame connection data -/
namespace Artform.Scores.GravityBridge.Statement
/-- **GAC:metric-frame-kinematics** (metric jets and independent frame connection data). -/
@[ledger "GAC:metric-frame-kinematics"]
def metricFrameLaw : Prop :=
  ((∀ i j, metricFromFrame finiteLorentzFrame i j =
      metricFromFrame (1 : Matrix (Fin 4) (Fin 4) ℚ) i j) ∧
    finiteLorentzFrame.det = 1 ∧ finiteLorentzFrame 0 1 = 4 / 3) ∧
  (∀ (b r : Fin 3 → ℚ),
    ∀ i j, coframeMetricVariation (lorentzGenerator b r) i j = 0) ∧
  (∀ (F : Matrix (Fin 4) (Fin 4) ℚ),
    (∀ i j, coframeMetricVariation F i j = 0) ↔
      ∃ b r : Fin 3 → ℚ, F = lorentzGenerator b r) ∧
  (Function.Injective (fun br : (Fin 3 → ℚ) × (Fin 3 → ℚ) => lorentzGenerator br.1 br.2)) ∧
  (∀ (N : ℕ)
    (F : Fin N → Matrix (Fin 4) (Fin 4) ℚ),
    (∀ n i j, coframeMetricVariation (F n) i j = 0) ↔
      ∃ b r : Fin N → Fin 3 → ℚ, ∀ n, F n = lorentzGenerator (b n) (r n)) ∧
  (∀ (k : Fin 4 → ℚ) (F : Matrix (Fin 4) (Fin 4) ℚ),
    (∀ i j a, linearTorsionSymbol k F (pureFrameConnection k F) i j a = 0) ∧
    (∀ i j a b, linearCurvatureSymbol k (pureFrameConnection k F) i j a b = 0)) ∧
  (∀ (k : Fin 4 → ℚ) (b r : Fin 3 → ℚ) (i a c : Fin 4),
    coframeMetricVariation (pureFrameConnection k (lorentzGenerator b r) i) a c = 0)
end Artform.Scores.GravityBridge.Statement
