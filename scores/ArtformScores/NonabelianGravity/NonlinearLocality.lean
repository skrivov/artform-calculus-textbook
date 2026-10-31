import ArtformScores.NonabelianGravity.NonlinearIncidence

/-! # Exact original one-step lapse incidence, with arbitrary neighbor data -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic
open scoped Matrix.Norms.Elementwise

lemma curvature_future_lapse_independent (E : ℕ → Mat)
    (U V : ℕ → Fin 4 → Mat) (s : ℝ) (r : Fin 6) :
    cellCurvatureFace (bumpAt E 1 s) U V r = cellCurvatureFace E U V r := by
  simp only [cellCurvatureFace, average_future_lapse_independent]

set_option maxHeartbeats 2000000 in
-- Temporal complements contain only spatial columns even with arbitrary transports.
lemma average_current_temporal_independent (E : ℕ → Mat) (V : ℕ → Fin 4 → Mat)
    (s : ℝ) (r : Fin 6) (hr : r.val < 3) :
    cellAverage (bumpAt E 0 s) V r = cellAverage E V r := by
  funext a
  fin_cases r <;> norm_num at hr
  all_goals fin_cases a <;>
    norm_num [cellAverage, transported, wedgeColumns, bumpAt, lapse, face,
      complement, NonlinearIsotropic.shift, Matrix.mul_apply]

lemma inverseLinks_lapse_line (q : Env) (s : ℝ) :
    inverseLinks (q + s • lapseDirection) = inverseLinks q := by
  funext t k
  simp [inverseLinks, links, lapseDirection]

lemma frames_lapse_line (q : Env) (s : ℝ) :
    frames (q + s • lapseDirection) = bumpAt (frames q) 0 s := by
  funext t
  by_cases ht : t = 0 <;> simp [frames, bumpAt, lapseDirection, ht]

lemma average_temporal_line (q : Env) (s : ℝ) (r : Fin 6) (hr : r.val < 3) :
    cellAverage (frames (q + s • lapseDirection)) (inverseLinks (q + s • lapseDirection)) r =
      cellAverage (frames q) (inverseLinks q) r := by
  rw [inverseLinks_lapse_line, frames_lapse_line,
    average_current_temporal_independent _ _ s r hr]

lemma preceding_frames_lapse_line (q : Env) (s : ℝ) :
    precedingFrames (q + s • lapseDirection) = bumpAt (precedingFrames q) 1 s := by
  funext t
  by_cases ht : t = 1 <;> simp [precedingFrames, bumpAt, lapseDirection, ht]

lemma preceding_links_lapse_line (q : Env) (s : ℝ) :
    precedingLinks (q + s • lapseDirection) = precedingLinks q := by
  funext t k
  simp [precedingLinks, lapseDirection]

lemma preceding_curvature_lapse_line (q : Env) (s : ℝ) :
    precedingCurvature (q + s • lapseDirection) = precedingCurvature q := by
  simp only [precedingCurvature, preceding_frames_lapse_line, preceding_links_lapse_line,
    curvature_future_lapse_independent]

lemma preceding_torsion_lapse_line (q : Env) (s : ℝ) :
    precedingTorsion (q + s • lapseDirection) = precedingTorsion q := by
  simp only [precedingTorsion, preceding_frames_lapse_line, preceding_links_lapse_line,
    torsion_future_lapse_independent]

end Artform.Scores.NonabelianGravity.NonlinearAmbient
