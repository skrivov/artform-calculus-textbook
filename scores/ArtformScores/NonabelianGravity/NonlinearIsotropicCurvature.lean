import ArtformScores.NonabelianGravity.NonlinearIsotropicSource

/-! # Exact lapse dependence of every original nonlinear curvature face -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearIsotropic
open Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Each of the six original faces and all five transported complement terms.
lemma curvature_face_difference (C S ell a c : K) (f : Fin 6) :
    curvatureFace C S ell a c f - curvatureFace C S 1 a c f =
      if f.val < 3 then 0 else (ell - 1) * a * rawLapse C S / 3 := by
  fin_cases f <;>
    norm_num [curvatureFace, averaged, transported, wedgeColumns, frame,
      atFrame, link, atLink, shift, face, complement, holonomy, inverseHolonomy,
      bivPair, bivSign, internalStar, lieCoordinates, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, rawLapse] <;> ring

lemma curvature_difference (C S ell a c : K) :
    curvature C S ell a c - curvature C S 1 a c = (ell - 1) * a * rawLapse C S := by
  simp only [curvature, ← Finset.sum_sub_distrib, curvature_face_difference]
  norm_num [Fin.sum_univ_succ]
  ring

lemma curvature_closed_difference (C S ell a c : K) (h : C ^ 2 - S ^ 2 = 1) :
    curvature C S ell a c - curvature C S 1 a c = (ell - 1) * a * closedLapse C S := by
  rw [curvature_difference, raw_closed C S h]

end Artform.Scores.NonabelianGravity.NonlinearIsotropic
