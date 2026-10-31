import ArtformScores.GravityBridge.Native.Full40.FourGroupStatements
/-! # The guarded complete four-group longitudinal target -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]
omit [CharZero K] in
lemma target_zero_iff (j rho d4 : K) (hj : j ≠ 0) (hr : rho ≠ 0) (hd : d4 ≠ 0)
    (groups : Fin 4 → K) : normalizedTarget j rho d4 groups = 0 ↔ fourGroupValue groups = 0 := by
  unfold normalizedTarget
  rw [div_eq_zero_iff]
  have hprod : j * rho * d4 ≠ 0 := mul_ne_zero (mul_ne_zero hj hr) hd
  simp [hprod]
lemma target_connection_zero_iff (j rho d4 : K) (hj : j ≠ 0) (hr : rho ≠ 0) (hd : d4 ≠ 0)
    (n : Fin 3 → K) (hn : ∃ a, n a ≠ 0) (groups : Fin 4 → K) :
    temporalBoostContact n (normalizedTarget j rho d4 groups) = 0 ↔ fourGroupValue groups = 0 := by
  rw [temporal_contact_zero_iff n hn, target_zero_iff j rho d4 hj hr hd]
omit [CharZero K] in
lemma four_group_sum (groups : Fin 4 → K) : fourGroupValue groups =
    groups 0 + groups 1 + groups 2 + groups 3 := by
  simp [fourGroupValue, Fin.sum_univ_succ]
  ring
lemma omitted_group_can_cancel :
    fourGroupValue (![1, -1, 0, 0] : Fin 4 → ℚ) = 0 ∧
      (![1, -1, 0, 0] : Fin 4 → ℚ) 0 ≠ 0 := by decide +kernel
lemma derivative_readout_does_not_fix_value :
    HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 ∧
    HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 ∧ (1 : ℝ) ≠ 0 :=
  ⟨hasDerivAt_const _ _, hasDerivAt_const _ _, one_ne_zero⟩
/-- **GAC2:guarded-four-group-target**
(the guarded complete four-group longitudinal target). -/
@[ledger "GAC2:guarded-four-group-target"]
theorem fourGroupLaw : Statement.fourGroupLaw := by
  intro K _ _
  exact ⟨target_zero_iff,
    target_connection_zero_iff,
    four_group_sum,
    omitted_group_can_cancel,
    derivative_readout_does_not_fix_value⟩
/-! ## Non-vacuity -/
example : temporalBoostContact (![1, 0, 0] : Fin 3 → ℚ)
    (normalizedTarget 1 1 1 ![1, 0, 0, 0]) = ![-1 / 4, 0, 0, 0, 0, 0] := by
  rw [temporal_contact_quarter]
  norm_num [normalizedTarget, fourGroupValue, Fin.sum_univ_succ]
end Artform.Scores.GravityBridge.Native.Full40
