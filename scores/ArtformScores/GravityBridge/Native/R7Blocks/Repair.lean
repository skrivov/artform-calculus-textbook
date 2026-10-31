import ArtformScores.GravityBridge.Native.R7Blocks.RepairStatements

/-! # The graph gap and whole-trace head normalization -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma riccati_norm_bound (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) (a : ℝ)
    (h11 : ‖A11‖ ≤ a) (h12 : ‖A12‖ ≤ a) (h22 : ‖A22‖ ≤ a)
    (hRic : blockDefect A11 A12 A21 A22 K = 0) :
    ‖A21‖ ≤ 2 * a * ‖K‖ + a * ‖K‖ ^ 2 := by
  have ha : 0 ≤ a := (norm_nonneg _).trans h11
  have he : A21 = K.comp (ownDataAction A11 A12 K) - A22.comp K := by
    have := hRic
    unfold blockDefect at this
    exact eq_sub_iff_add_eq.mpr (sub_eq_zero.mp this)
  rw [he]
  calc
    _ ≤ ‖K.comp (ownDataAction A11 A12 K)‖ + ‖A22.comp K‖ := norm_sub_le _ _
    _ ≤ ‖K‖ * ‖ownDataAction A11 A12 K‖ + ‖A22‖ * ‖K‖ := by
      gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖K‖ * (‖A11‖ + ‖A12‖ * ‖K‖) + ‖A22‖ * ‖K‖ := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add_right
        (ContinuousLinearMap.opNorm_comp_le A12 K) _)
    _ ≤ ‖K‖ * (a + a * ‖K‖) + a * ‖K‖ := by gcongr
    _ = 2 * a * ‖K‖ + a * ‖K‖ ^ 2 := by ring

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
lemma graph_gap_positive (a d : ℝ) (ha : 0 < a) (hd : 0 < d) : 0 < graphGap a d := by
  have hp : 0 < d / (2 * a) := div_pos hd (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 1 + d / (2 * a) by positivity)
  have hn := Real.sqrt_nonneg (1 + d / (2 * a))
  unfold graphGap
  nlinarith

lemma complete_uniform_graph_gap (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) (a d : ℝ)
    (ha : 0 < a) (_hd : 0 < d) (h21 : d / 2 ≤ ‖A21‖)
    (h11 : ‖A11‖ ≤ a) (h12 : ‖A12‖ ≤ a) (h22 : ‖A22‖ ≤ a)
    (hRic : blockDefect A11 A12 A21 A22 K = 0) : graphGap a d ≤ ‖K‖ := by
  have hb := h21.trans (riccati_norm_bound A11 A12 A21 A22 K a h11 h12 h22 hRic)
  have hn := norm_nonneg K
  have hr : 1 + d / (2 * a) ≤ (‖K‖ + 1) ^ 2 := by
    have hv : d / (2 * a) ≤ 2 * ‖K‖ + ‖K‖ ^ 2 :=
      (div_le_iff₀ (show 0 < 2 * a by positivity)).2 (by nlinarith)
    nlinarith
  have hs : Real.sqrt (1 + d / (2 * a)) ≤ ‖K‖ + 1 :=
    (Real.sqrt_le_iff).2 ⟨by positivity, hr⟩
  exact sub_le_iff_le_add.mpr hs

lemma prepared_graph_distance (K K₀ : Y →L[ℝ] Z) (c : ℝ)
    (hK : c ≤ ‖K‖) (h₀ : ‖K₀‖ ≤ c / 2) : c / 2 ≤ ‖K - K₀‖ := by
  have hn := norm_le_insert' K K₀
  linarith

lemma head_neumann_inverse [CompleteSpace Y] [Nontrivial Y]
    (D : Y →L[ℝ] Y) (δ : ℝ) (hD : ‖D‖ ≤ δ) (hδ : δ < 1) :
    ∃ J : Y →L[ℝ] Y,
      (ContinuousLinearMap.id ℝ Y + D).comp J = ContinuousLinearMap.id ℝ Y ∧
      J.comp (ContinuousLinearMap.id ℝ Y + D) = ContinuousLinearMap.id ℝ Y ∧
      ‖J‖ ≤ 1 / (1 - δ) := by
  have hd : ‖-D‖ < 1 := by simpa only [norm_neg] using hD.trans_lt hδ
  let u := Units.oneSub (-D) hd
  refine ⟨↑u⁻¹, ?_, ?_, ?_⟩
  · change ((1 : Y →L[ℝ] Y) + D) * ↑u⁻¹ = 1
    have he : (u : Y →L[ℝ] Y) = 1 + D := by simp [u]
    rw [← he]
    exact congrArg Units.val (mul_inv_cancel u)
  · change ↑u⁻¹ * ((1 : Y →L[ℝ] Y) + D) = 1
    have he : (u : Y →L[ℝ] Y) = 1 + D := by simp [u]
    rw [← he]
    exact congrArg Units.val (inv_mul_cancel u)
  · change ‖∑' n : ℕ, (-D) ^ n‖ ≤ 1 / (1 - δ)
    have hb := tsum_geometric_le_of_norm_lt_one (-D) hd
    simp only [norm_neg, norm_one, sub_self, zero_add] at hb
    apply hb.trans
    rw [one_div]
    gcongr

lemma repair_normalization_algebra
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E Δ : Y →L[ℝ] H) (Q : H →L[ℝ] Y) (R : H →L[ℝ] Z)
    (K : Y →L[ℝ] Z) (J : Y →L[ℝ] Y)
    (hQE : Q.comp E = ContinuousLinearMap.id ℝ Y) (hRE : R.comp E = K)
    (hhead : (ContinuousLinearMap.id ℝ Y + Q.comp Δ).comp J = ContinuousLinearMap.id ℝ Y)
    (hhead' : J.comp (ContinuousLinearMap.id ℝ Y + Q.comp Δ) = ContinuousLinearMap.id ℝ Y) :
    Q.comp ((E + Δ).comp J) = ContinuousLinearMap.id ℝ Y ∧
    R.comp ((E + Δ).comp J) = (K + R.comp Δ).comp J ∧
    Set.range ((E + Δ).comp J) = Set.range (E + Δ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_add, hQE]
    exact hhead
  · rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_add, hRE]
  · ext w
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨J y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(ContinuousLinearMap.id ℝ Y + Q.comp Δ) y, ?_⟩
      have hj := congrArg (fun T : Y →L[ℝ] Y => T y) hhead'
      change (E + Δ) (J ((ContinuousLinearMap.id ℝ Y + Q.comp Δ) y)) = (E + Δ) y
      rw [show J ((ContinuousLinearMap.id ℝ Y + Q.comp Δ) y) = y from hj]

lemma normalized_repair_norm
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Y →L[ℝ] Z) (Δ : Y →L[ℝ] H) (R : H →L[ℝ] Z) (J : Y →L[ℝ] Y)
    (δ : ℝ) (hR : ‖R‖ ≤ 1) (hΔ : ‖Δ‖ ≤ δ) (_hδ : δ < 1)
    (hJ : ‖J‖ ≤ 1 / (1 - δ)) : ‖(K + R.comp Δ).comp J‖ ≤ (‖K‖ + δ) / (1 - δ) := by
  have hd : 0 ≤ δ := (norm_nonneg _).trans hΔ
  have hRD : ‖R‖ * ‖Δ‖ ≤ δ := by
    calc
      _ ≤ 1 * δ := by gcongr
      _ = δ := one_mul δ
  calc
    _ ≤ ‖K + R.comp Δ‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖K‖ + ‖R‖ * ‖Δ‖) * ‖J‖ := by
      gcongr
      exact (norm_add_le _ _).trans
        (add_le_add_right (ContinuousLinearMap.opNorm_comp_le R Δ) _)
    _ ≤ (‖K‖ + δ) * (1 / (1 - δ)) := by gcongr
    _ = (‖K‖ + δ) / (1 - δ) := by ring

lemma repair_gap_scalar (c k δ : ℝ) (hc : 0 ≤ c) (hk : 0 ≤ k) (_hd : 0 ≤ δ)
    (hsmall : δ < 1 → c ≤ (k + δ) / (1 - δ)) : (c - k) / (1 + c) ≤ δ := by
  apply (div_le_iff₀ (show 0 < 1 + c by positivity)).2
  by_cases hδ : δ < 1
  · have h := (le_div_iff₀ (show 0 < 1 - δ by linarith)).mp (hsmall hδ)
    nlinarith
  · have hl : 1 ≤ δ := le_of_not_gt hδ
    nlinarith

lemma whole_trace_repair_gap [CompleteSpace Y] [Nontrivial Y]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Y →L[ℝ] Z) (Δ : Y →L[ℝ] H) (Q : H →L[ℝ] Y) (R : H →L[ℝ] Z)
    (c : ℝ) (hc : 0 ≤ c) (hQ : ‖Q‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hgap : ∀ J : Y →L[ℝ] Y,
      (ContinuousLinearMap.id ℝ Y + Q.comp Δ).comp J = ContinuousLinearMap.id ℝ Y →
      J.comp (ContinuousLinearMap.id ℝ Y + Q.comp Δ) = ContinuousLinearMap.id ℝ Y →
      c ≤ ‖(K + R.comp Δ).comp J‖) : (c-‖K‖) / (1 + c) ≤ ‖Δ‖ := by
  apply repair_gap_scalar c ‖K‖ ‖Δ‖ hc (norm_nonneg _) (norm_nonneg _)
  intro hδ
  have hd : ‖Q.comp Δ‖ ≤ ‖Δ‖ := by
    calc
      _ ≤ ‖Q‖ * ‖Δ‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖Δ‖ := mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
      _ = ‖Δ‖ := one_mul _
  obtain ⟨J, hleft, hright, hbound⟩ := head_neumann_inverse (Q.comp Δ) ‖Δ‖ hd hδ
  exact (hgap J hleft hright).trans
    (normalized_repair_norm K Δ R J ‖Δ‖ hR le_rfl hδ hbound)

lemma fixed_prepared_repair_gap (c k δ : ℝ) (hc : 0 < c) (hk : k ≤ c / 2)
    (hgap : (c - k) / (1 + c) ≤ δ) : c / (2 * (1 + c)) ≤ δ := by
  have hden : 0 < 1 + c := by positivity
  apply le_trans _ hgap
  apply (div_le_div_iff₀ (show 0 < 2 * (1 + c) by positivity) hden).2
  nlinarith

/-- **GAC2:whole-trace-repair-gap**
(the graph gap and whole-trace head normalization). -/
@[ledger "GAC2:whole-trace-repair-gap"]
theorem repairLaw : Statement.repairLaw := by
  intro Y Z _ _ _ _
  exact ⟨riccati_norm_bound,
    graph_gap_positive,
    complete_uniform_graph_gap,
    prepared_graph_distance,
    head_neumann_inverse,
    repair_normalization_algebra,
    normalized_repair_norm,
    repair_gap_scalar,
    whole_trace_repair_gap,
    fixed_prepared_repair_gap⟩

/-! ## Non-vacuity -/


example : graphGap 1 2 > 0 ∧ graphGap 1 2 ≤ ‖(ContinuousLinearMap.id ℝ ℝ)‖ := by
  constructor
  · exact graph_gap_positive 1 2 (by norm_num) (by norm_num)
  · apply complete_uniform_graph_gap (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)
      (ContinuousLinearMap.id ℝ ℝ) 0 (ContinuousLinearMap.id ℝ ℝ) 1 2
    all_goals try norm_num
    apply ContinuousLinearMap.ext
    intro x
    simp [blockDefect, ownDataAction]



example : ∃ J : ℝ →L[ℝ] ℝ,
    (ContinuousLinearMap.id ℝ ℝ + (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).comp J =
      ContinuousLinearMap.id ℝ ℝ ∧
    J.comp (ContinuousLinearMap.id ℝ ℝ + (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ ∧ ‖J‖ ≤ 1 / (1 - (1 / 2 : ℝ)) := by
  apply head_neumann_inverse ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (1 / 2)
  all_goals norm_num [norm_smul]

end Artform.Scores.GravityBridge.Native.R7Blocks
