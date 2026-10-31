import ArtformScores.GravityBridge.StateTopologyStatements
/-! # Actual positive states and the topology distinction -/
namespace Artform.Scores.GravityBridge
noncomputable section
lemma evaluation_state_positive (x : StateInterval) :
    evaluationState x 1 = 1 ∧ ∀ f : C(StateInterval, ℝ), 0 ≤ evaluationState x (f * f) := by
  refine ⟨rfl, ?_⟩
  intro f
  change 0 ≤ f x * f x
  exact mul_self_nonneg _
lemma evaluation_state_bound (x : StateInterval) : ‖evaluationState x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa [evaluationState] using f.norm_coe_le_norm x
lemma separating_state_function (x : StateInterval) (hx : 0 < (x : ℝ)) :
    ‖separatingStateFunction x‖ ≤ 1 ∧
    separatingStateFunction x stateZeroPoint = 1 ∧ separatingStateFunction x x = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · apply (ContinuousMap.norm_le _ (by norm_num)).mpr
    intro t
    change |max (-1 : ℝ) (1 - 2 * (t : ℝ) / (x : ℝ))| ≤ 1
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · apply max_le (by norm_num)
      have ht : 0 ≤ 2 * (t : ℝ) / (x : ℝ) := div_nonneg (by nlinarith [t.property.1]) hx.le
      linarith
  · norm_num [separatingStateFunction, stateZeroPoint]
  · norm_num [separatingStateFunction, div_self (ne_of_gt hx)]
    field_simp
    norm_num
lemma evaluation_state_distance (x : StateInterval) (hx : 0 < (x : ℝ)) :
    ‖evaluationState x - evaluationState stateZeroPoint‖ = 2 := by
  apply le_antisymm
  · calc
      ‖evaluationState x - evaluationState stateZeroPoint‖ ≤
          ‖evaluationState x‖ + ‖evaluationState stateZeroPoint‖ :=
        norm_sub_le (evaluationState x) (evaluationState stateZeroPoint)
      _ ≤ 2 := by linarith [evaluation_state_bound x, evaluation_state_bound stateZeroPoint]
  · obtain ⟨hb, h0, hx0⟩ := separating_state_function x hx
    have h := (evaluationState x - evaluationState stateZeroPoint).le_opNorm
      (separatingStateFunction x)
    have he : (evaluationState x - evaluationState stateZeroPoint)
        (separatingStateFunction x) = -2 := by
      change separatingStateFunction x x - separatingStateFunction x stateZeroPoint = -2
      rw [hx0, h0]
      norm_num
    rw [he] at h
    norm_num at h
    have hm := mul_le_mul_of_nonneg_left hb
      (norm_nonneg (evaluationState x - evaluationState stateZeroPoint))
    nlinarith
lemma evaluation_states_pointwise_limit (f : C(StateInterval, ℝ)) :
    Filter.Tendsto (fun n => evaluationState (movingStatePoint n) f)
      Filter.atTop (nhds (evaluationState stateZeroPoint f)) := by
  have ht : Filter.Tendsto movingStatePoint Filter.atTop (nhds stateZeroPoint) := by
    apply tendsto_subtype_rng.mpr
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact f.continuous.continuousAt.tendsto.comp ht
lemma evaluation_states_norm_distance (n : ℕ) :
    ‖evaluationState (movingStatePoint n) - evaluationState stateZeroPoint‖ = 2 := by
  apply evaluation_state_distance
  dsimp [movingStatePoint]
  positivity
lemma evaluation_states_no_norm_limit :
    ¬ Filter.Tendsto
      (fun n : ℕ => ‖evaluationState (movingStatePoint n) - evaluationState stateZeroPoint‖)
      Filter.atTop (nhds 0) := by
  simp_rw [evaluation_states_norm_distance]
  intro h
  have he : (2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h
  norm_num at he
/-- **GAC:state-topology-audit** (actual positive states and the topology distinction). -/
@[ledger "GAC:state-topology-audit"]
theorem stateTopologyLaw : Statement.stateTopologyLaw := by
  exact ⟨evaluation_state_positive,
    evaluation_state_bound,
    separating_state_function,
    evaluation_state_distance,
    evaluation_states_pointwise_limit,
    evaluation_states_norm_distance,
    evaluation_states_no_norm_limit⟩
/-! ## Non-vacuity -/
example : ∀ n : ℕ, ‖evaluationState (movingStatePoint n) - evaluationState stateZeroPoint‖ = 2 := by
  intro n
  apply evaluation_state_distance
  dsimp [movingStatePoint]
  positivity
end
end Artform.Scores.GravityBridge
