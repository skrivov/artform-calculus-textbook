import ArtformScores.NonabelianGravity.NonlinearIsotropicSource

/-! # The declared nonlinear links are actual proper Lorentz matrices -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearIsotropic
open Artform.Scores.GravityBridge.Native.Full40

set_option maxHeartbeats 2000000 in
-- The ordered reverse words in the original action use these exact inverses.
lemma link_inverse (C S : ℝ) (h : C ^ 2 - S ^ 2 = 1) (k : Fin 4) :
    link C (-S) k * link C S k = 1 := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [link, Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith

set_option maxHeartbeats 2000000 in
-- The signature remains (-,+,+,+) in the original ordered internal frame.
lemma link_lorentz (C S : ℝ) (h : C ^ 2 - S ^ 2 = 1) (k : Fin 4) :
    (link C S k).transpose * Matrix.diagonal (fun i => (eta i : ℝ)) * link C S k =
      Matrix.diagonal (fun i => (eta i : ℝ)) := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [link, eta, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal,
      Fin.sum_univ_succ] <;> nlinarith

set_option maxHeartbeats 2000000 in
-- Expansion of the actual four-by-four determinant, not an assumed group tag.
lemma link_det (C S : ℝ) (h : C ^ 2 - S ^ 2 = 1) (k : Fin 4) :
    (link C S k).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  fin_cases k <;>
    norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
      link, Fin.succAbove] <;> nlinarith

end Artform.Scores.NonabelianGravity.NonlinearIsotropic
