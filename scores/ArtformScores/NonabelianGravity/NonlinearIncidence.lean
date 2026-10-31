import ArtformScores.NonabelianGravity.NonlinearSmooth

/-! # Exact original one-step lapse incidence, with arbitrary neighbor data -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic
open scoped Matrix.Norms.Elementwise

noncomputable def bumpAt (E : ℕ → Mat) (site : ℕ) (s : ℝ) : ℕ → Mat :=
  fun t => E t + if t = site then s • lapse else 0

set_option maxHeartbeats 2000000 in
-- Both original diagonal transports are kept; no old-frame/link restriction.
lemma average_future_lapse_independent (E : ℕ → Mat) (V : ℕ → Fin 4 → Mat)
    (s : ℝ) (r : Fin 6) : cellAverage (bumpAt E 1 s) V r = cellAverage E V r := by
  funext a
  fin_cases r <;> fin_cases a <;>
    norm_num [cellAverage, transported, wedgeColumns, bumpAt, lapse, face,
      complement, NonlinearIsotropic.shift, Matrix.mul_apply]

set_option maxHeartbeats 1000000 in
-- The incoming forward torsion reads only the future spatial coframe columns.
lemma torsion_future_lapse_independent (E : ℕ → Mat) (V : ℕ → Fin 4 → Mat)
    (s : ℝ) (r : Fin 6) :
    cellTorsionFace (bumpAt E 1 s) V r = cellTorsionFace E V r := by
  funext i
  fin_cases r <;> fin_cases i <;>
    norm_num [cellTorsionFace, bumpAt, lapse, face, NonlinearIsotropic.shift, Matrix.mul_apply]

end Artform.Scores.NonabelianGravity.NonlinearAmbient
