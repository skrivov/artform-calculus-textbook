import ArtformScores.GravityBridge.StateTopologyDefs
/-! # Actual positive states and the topology distinction -/
namespace Artform.Scores.GravityBridge.Statement
/-- **GAC:state-topology-audit** (actual positive states and the topology distinction). -/
@[ledger "GAC:state-topology-audit"]
def stateTopologyLaw : Prop :=
  (∀ (x : StateInterval),
    evaluationState x 1 = 1 ∧ ∀ f : C(StateInterval, ℝ), 0 ≤ evaluationState x (f * f)) ∧
  (∀ (x : StateInterval),
    ‖evaluationState x‖ ≤ 1) ∧
  (∀ (x : StateInterval) (_hx : 0 < (x : ℝ)),
    ‖separatingStateFunction x‖ ≤ 1 ∧
    separatingStateFunction x stateZeroPoint = 1 ∧ separatingStateFunction x x = -1) ∧
  (∀ (x : StateInterval) (_hx : 0 < (x : ℝ)),
    ‖evaluationState x - evaluationState stateZeroPoint‖ = 2) ∧
  (∀ (f : C(StateInterval, ℝ)),
    Filter.Tendsto (fun n => evaluationState (movingStatePoint n) f)
      Filter.atTop (nhds (evaluationState stateZeroPoint f))) ∧
  (∀ (n : ℕ),
    ‖evaluationState (movingStatePoint n) - evaluationState stateZeroPoint‖ = 2) ∧
  (¬ Filter.Tendsto
      (fun n : ℕ => ‖evaluationState (movingStatePoint n) - evaluationState stateZeroPoint‖)
      Filter.atTop (nhds 0))
end Artform.Scores.GravityBridge.Statement
