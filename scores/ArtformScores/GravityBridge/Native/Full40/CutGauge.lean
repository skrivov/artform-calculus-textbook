import ArtformScores.GravityBridge.Native.Full40.CutGaugeStatements
/-! # Six-component native cut gauge readouts and their forward frame cost -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {X : Type*} [AddCommGroup X]
lemma cut_gauge_frame_zero (h : ℝ) (d : Fin 3 → X) (c : X → Biv ℝ) (x : X) :
    (cutGauge h d c (0, x)).1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cutGauge, gaugeField, cutGamma, bounded_profile_cut, lie]
lemma cut_gauge_temporal_link (h : ℝ) (hh : h ≠ 0) (d : Fin 3 → X)
    (c : X → Biv ℝ) (x : X) : (cutGauge h d c (0, x)).2 0 = c x := by
  simp [cutGauge, gaugeField, gaugeConnection, cutDirections, cutGamma,
    bounded_profile_cut, bounded_profile_value h 1 hh]
lemma cut_gauge_spatial_links (h : ℝ) (d : Fin 3 → X) (c : X → Biv ℝ)
    (x : X) (i : Fin 3) : (cutGauge h d c (0, x)).2 i.succ = 0 := by
  fin_cases i <;> simp [cutGauge, gaugeField, gaugeConnection, cutDirections, cutGamma,
    bounded_profile_cut]
lemma cut_gauge_frame_derivative (h : ℝ) (d : Fin 3 → X) (c : X → Biv ℝ)
    (x : X) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => (cutGauge h d c (t, x)).1 i j) 0 0 := by
  have he : (fun t : ℝ => (cutGauge h d c (t, x)).1 i j) =
      (fun t => boundedTemporalProfile h 1 t * lie (c x) i j) := by
    funext t
    simp only [cutGauge, gaugeField, cutGamma, lie_smul, Matrix.smul_apply, smul_eq_mul]
  rw [he]
  convert (bounded_profile_derivative h 1).mul_const (lie (c x) i j) using 1
  simp
lemma cut_gauge_metric_zero (h : ℝ) (d : Fin 3 → X) (c : X → Biv ℝ)
    (tx : ℝ × X) (i j : Fin 4) : metricVariation (cutGauge h d c tx).1 i j = 0 :=
  lie_metric_kernel (cutGamma h c tx) i j
lemma cut_gauge_forward_frame (h : ℝ) (hh : h ≠ 0) (d : Fin 3 → X)
    (c : X → Biv ℝ) (x : X) : (cutGauge h d c (h, x)).1 = lie (c x) := by
  simp [cutGauge, gaugeField, cutGamma, bounded_profile_value h 1 hh]
lemma full_forward_frame_blocks_temporal_adjustment (h : ℝ) (hh : h ≠ 0)
    (d : Fin 3 → X) (c : X → Biv ℝ) (x : X)
    (hc : (cutGauge h d c (h, x)).1 = 0) : c x = 0 := by
  rw [cut_gauge_forward_frame h hh d c x] at hc
  have hz : lie (0 : Biv ℝ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lie]
  exact lie_injective (hc.trans hz.symm)
/-- **GAC2:native-cut-gauge-readouts**
(six-component native cut gauge readouts and their forward frame cost). -/
@[ledger "GAC2:native-cut-gauge-readouts"]
theorem cutGaugeLaw : Statement.cutGaugeLaw := by
  intro X _
  exact ⟨cut_gauge_frame_zero,
    cut_gauge_temporal_link,
    cut_gauge_spatial_links,
    cut_gauge_frame_derivative,
    cut_gauge_metric_zero,
    cut_gauge_forward_frame,
    full_forward_frame_blocks_temporal_adjustment⟩
/-! ## Non-vacuity -/
example : (cutGauge (1 : ℝ) (fun _ : Fin 3 => (0 : ℤ))
    (fun _ => ![1, 0, 0, 0, 0, 0]) (0, 0)).2 0 = ![1, 0, 0, 0, 0, 0] :=
  cut_gauge_temporal_link 1 (by norm_num) _ _ _
end Artform.Scores.GravityBridge.Native.Full40
