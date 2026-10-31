import ArtformScores.NonabelianGravity.NonlinearIsotropicSource

/-! # The preceding incident curvature cell is independent of the varied lapse -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearIsotropic
open Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Identity incoming links, full future boost links and every original face.
lemma incoming_face_independent (C S ell a : K) (f : Fin 6) :
    cellCurvatureFace (incomingFrame ell a) (incomingLink C S) (incomingLink C (-S)) f =
      cellCurvatureFace (incomingFrame 1 a) (incomingLink C S) (incomingLink C (-S)) f := by
  fin_cases f <;>
    norm_num [cellCurvatureFace, cellAverage, transported, wedgeColumns, frame,
      incomingFrame, link, incomingLink, shift, face, complement, cellHolonomy,
      cellInverseHolonomy, bivPair, bivSign, internalStar, lieCoordinates,
      Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ]

lemma incoming_curvature_independent (C S ell a : K) :
    incomingCurvature C S ell a = incomingCurvature C S 1 a := by
  simp only [incomingCurvature, incoming_face_independent]

end Artform.Scores.NonabelianGravity.NonlinearIsotropic
