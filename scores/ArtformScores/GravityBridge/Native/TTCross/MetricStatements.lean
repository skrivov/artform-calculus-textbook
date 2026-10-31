import ArtformScores.GravityBridge.Native.TTCross.MetricDefs

/-! # Metric cost of the full paired-axis preparation -/

namespace Artform.Scores.GravityBridge.Native.TTCross.Statement

open Matrix CoordinateSymbol Full40

/-- **GAC2:native-prepared-metric-cut-cost**
(metric cost of the full paired-axis preparation). -/
@[ledger "GAC2:native-prepared-metric-cut-cost"]
def metricLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (j a : K) (_ha : a ≠ 0) (u : Fin 2 → K),
    preparedMetricCut j a u 0 3 = u 0 ∧
    preparedMetricCut j a u 1 3 = -j * u 1 / (2 * a) ∧
    preparedMetricCut j a u 2 3 = j * u 1 / (2 * a)) ∧
    (∀ (j a : K) (_hj : j ^ 2 = -1) (_ha : a ≠ 0)
    (u : Fin 2 → K),
    preparedMetricCut j a u = 0 ↔ u = 0) ∧
    (∀ (j a : K) (_hj : j ^ 2 = -1) (_ha : a ≠ 0)
    (u : Fin 2 → K) (L : Matrix (Fin 4) (Fin 4) K) (_hL : L = 0),
    preparedMetricCut j a u + L = 0 ↔ u = 0)

end Artform.Scores.GravityBridge.Native.TTCross.Statement
