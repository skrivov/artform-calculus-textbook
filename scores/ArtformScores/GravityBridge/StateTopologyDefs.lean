import ArtformScores.GravityBridge.LinearDefs
/-! # Actual positive states and the topology distinction -/
namespace Artform.Scores.GravityBridge
noncomputable section
abbrev StateInterval := Set.Icc (0 : ℝ) 1
def stateZeroPoint : StateInterval := ⟨0, by constructor <;> norm_num⟩
def evaluationState (x : StateInterval) : C(StateInterval, ℝ) →L[ℝ] ℝ :=
  ContinuousMap.evalCLM ℝ x
def movingStatePoint (n : ℕ) : StateInterval :=
  ⟨1 / ((n : ℝ) + 1), by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    constructor
    · positivity
    · rw [div_le_one hn]
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)⟩
def separatingStateFunction (x : StateInterval) : C(StateInterval, ℝ) where
  toFun t := max (-1) (1 - 2 * (t : ℝ) / (x : ℝ))
  continuous_toFun := by fun_prop
end
end Artform.Scores.GravityBridge
