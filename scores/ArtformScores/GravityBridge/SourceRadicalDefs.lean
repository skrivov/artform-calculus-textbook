import ArtformScores.GravityBridge.Radical
/-! # Sources constrain the allowable radical quotient -/
namespace Artform.Scores.GravityBridge
noncomputable section
def sourceCompatibleNull (j k : ℚ) : Submodule ℚ GaugeSpace :=
  gaugeNull ⊓ LinearMap.ker (visibleSource j + k • hiddenSource)
end
end Artform.Scores.GravityBridge
