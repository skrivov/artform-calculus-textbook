import ArtformScores.GravityBridge.Native.Full40.TemporalProfile
/-! # Six-component native cut gauge readouts and their forward frame cost -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {X : Type*} [AddCommGroup X]
noncomputable def cutGamma (h : ℝ) (c : X → Biv ℝ) (tx : ℝ × X) : Biv ℝ :=
  boundedTemporalProfile h 1 tx.1 • c tx.2
def cutDirections (h : ℝ) (d : Fin 3 → X) : Fin 4 → ℝ × X :=
  ![(h, 0), (0, d 0), (0, d 1), (0, d 2)]
noncomputable def cutGauge (h : ℝ) (d : Fin 3 → X) (c : X → Biv ℝ) :
    NativeField (ℝ × X) ℝ := gaugeField (cutDirections h d) (cutGamma h c)
end Artform.Scores.GravityBridge.Native.Full40
