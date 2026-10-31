import ArtformScores.GravityBridge.Native.TTCross.MetricStatements

/-! # Metric cost of the full paired-axis preparation -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

open Matrix
lemma actual_prepared_metric_entries (j a : K) (ha : a ≠ 0) (u : Fin 2 → K) :
    preparedMetricCut j a u 0 3 = u 0 ∧
    preparedMetricCut j a u 1 3 = -j * u 1 / (2 * a) ∧
    preparedMetricCut j a u 2 3 = j * u 1 / (2 * a) := by
  norm_num [preparedMetricCut, preparedJet]
  constructor <;> field_simp

lemma metric_cut_observes_all_TT_data (j a : K) (hj : j ^ 2 = -1) (ha : a ≠ 0)
    (u : Fin 2 → K) : preparedMetricCut j a u = 0 ↔ u = 0 := by
  have hj0 : j ≠ 0 := by intro h;rw [h] at hj;norm_num at hj
  have hh := actual_prepared_metric_entries j a ha u
  constructor
  · intro h
    have hq : u 0 = 0 := by simpa only [h, Matrix.zero_apply] using hh.1.symm
    have hv : u 1 = 0 := by
      have hz : -j * u 1 / (2 * a) = 0 := by rw [← hh.2.1, h];rfl
      have ht : -j * u 1 = 0 := (div_eq_zero_iff.mp hz).resolve_right
        (mul_ne_zero (by norm_num) ha)
      exact (mul_eq_zero.mp ht).resolve_left (neg_ne_zero.mpr hj0)
    ext i
    fin_cases i <;> assumption
  · intro h
    subst u
    ext i l
    fin_cases i <;> fin_cases l <;> simp [preparedMetricCut, preparedJet]

lemma zero_Lorentz_metric_cannot_cancel (j a : K) (hj : j ^ 2 = -1) (ha : a ≠ 0)
    (u : Fin 2 → K) (L : Matrix (Fin 4) (Fin 4) K) (hL : L = 0) :
    preparedMetricCut j a u + L = 0 ↔ u = 0 := by
  rw [hL, add_zero]
  exact metric_cut_observes_all_TT_data j a hj ha u

/-- **GAC2:native-prepared-metric-cut-cost**
(metric cost of the full paired-axis preparation). -/
@[ledger "GAC2:native-prepared-metric-cut-cost"]
theorem metricLaw : Statement.metricLaw := by
  intro K _ _
  exact ⟨actual_prepared_metric_entries,
    metric_cut_observes_all_TT_data,
    zero_Lorentz_metric_cannot_cancel⟩

/-! ## Non-vacuity -/
example : preparedMetricCut Complex.I (1 : ℂ) ![0, 1] 1 3 = -Complex.I / 2 := by
  norm_num [preparedMetricCut, preparedJet]
  ring

end Artform.Scores.GravityBridge.Native.TTCross
