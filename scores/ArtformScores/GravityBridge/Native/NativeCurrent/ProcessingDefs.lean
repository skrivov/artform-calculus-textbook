import ArtformScores.GravityBridge.Stability

/-! # Complete pulled-current change and norm bound -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent

variable {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

noncomputable def pulledCurrent (B : H →L[ℝ] H →L[ℝ] ℝ) (E : Y →L[ℝ] H) : Y →L[ℝ] Y →L[ℝ] ℝ :=
  B.bilinearComp E E

end Artform.Scores.GravityBridge.Native.NativeCurrent
