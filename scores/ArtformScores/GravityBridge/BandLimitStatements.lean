import ArtformScores.GravityBridge.BandLimitDefs

/-! # Gaussian operator norm limit on a fixed band -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:gaussian-band-limit** (gaussian operator norm limit on a fixed band). -/
@[ledger "GAC:gaussian-band-limit"]
def bandLimitLaw : Prop :=
  (∀ h R : ℝ, 0 ≤ h → 0 ≤ R →
    ‖gaussianBandStep h R - ContinuousLinearMap.id ℝ C(FrequencyBand R, ℝ)‖ ≤ h * R ^ 2 / 2) ∧
  (∀ R : ℝ, 0 ≤ R → Filter.Tendsto
    (fun h : ℝ => ‖gaussianBandStep h R -
      ContinuousLinearMap.id ℝ C(FrequencyBand R, ℝ)‖)
    (nhdsWithin 0 (Set.Ici 0)) (nhds 0)) ∧
  (Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)) ∧
  (∀ n : ℕ,
    Real.exp (-(1 / ((n : ℝ) + 1)) * (Real.sqrt (2 * ((n : ℝ) + 1))) ^ 2 / 2) =
      Real.exp (-1)) ∧
  (0 < |Real.exp (-1 : ℝ) - 1|) ∧
  (¬ Filter.Tendsto (fun n : ℕ => |Real.exp (-(1 / ((n : ℝ) + 1)) *
    (Real.sqrt (2 * ((n : ℝ) + 1))) ^ 2 / 2) - 1|) Filter.atTop (nhds 0))

end Artform.Scores.GravityBridge.Statement
