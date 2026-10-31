import ArtformScores.GravityBridge.Native.Full40.CutJetsStatements
/-! # Exact coframe value and velocity recovery and its connection limit -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]
lemma cut_value_velocity_recovery (F G : Fin 2 → Frame K)
    (hm : ∀ n, metricVariation (F n) = metricVariation (G n))
    (hw : ∀ n, coframeLorentz (F n) = coframeLorentz (G n)) : F = G := by
  funext n
  exact split_readout_injective (F n) (G n) (hm n) (hw n)
lemma cut_recovery_iff (F G : Fin 2 → Frame K) : F = G ↔
    (∀ n, metricVariation (F n) = metricVariation (G n)) ∧
    (∀ n, coframeLorentz (F n) = coframeLorentz (G n)) := by
  constructor
  · rintro rfl
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rintro ⟨hm, hw⟩
    exact cut_value_velocity_recovery F G hm hw
lemma metric_only_does_not_fix_frame :
    metricVariation (lie (![1, 0, 0, 0, 0, 0] : Biv ℚ)) =
      metricVariation (0 : Frame ℚ) ∧
    lie (![1, 0, 0, 0, 0, 0] : Biv ℚ) ≠ 0 := by
  constructor
  · ext i j
    simpa only [metricVariation, Matrix.zero_apply, mul_zero, add_zero] using
      lie_metric_kernel (![1, 0, 0, 0, 0, 0] : Biv ℚ) i j
  · intro h
    have he := congrArg (fun F : Frame ℚ => F 0 1) h
    norm_num [lie] at he
lemma coframe_jets_do_not_fix_connection :
    ∃ Q R : Fin 2 → Full ℚ, (∀ n, (Q n).1 = (R n).1) ∧
      (Q 0).2 ≠ (R 0).2 := by
  refine ⟨fun _ => 0, fun _ => (0, fun _ => ![1, 0, 0, 0, 0, 0]), ?_, ?_⟩
  · intro n
    rfl
  · intro h
    have he := congrArg (fun A : Connection ℚ => A 0 0) h
    norm_num at he
/-- **GAC2:coframe-cut-value-velocity**
(exact coframe value and velocity recovery and its connection limit). -/
@[ledger "GAC2:coframe-cut-value-velocity"]
theorem cutJetsLaw : Statement.cutJetsLaw := by
  intro K _ _
  exact ⟨cut_value_velocity_recovery,
    cut_recovery_iff,
    metric_only_does_not_fix_frame,
    coframe_jets_do_not_fix_connection⟩
/-! ## Non-vacuity -/
example : (fun _ : Fin 2 => lie (![1, 2, 3, 4, 5, 6] : Biv ℚ)) =
    (fun _ : Fin 2 => lie (![1, 2, 3, 4, 5, 6] : Biv ℚ)) :=
  cut_value_velocity_recovery _ _ (fun _ => rfl) (fun _ => rfl)
end Artform.Scores.GravityBridge.Native.Full40
