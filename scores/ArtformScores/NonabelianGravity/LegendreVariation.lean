import ArtformScores.NonabelianGravity.LegendreBoundary
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # Actual real directional derivatives of the source-bound boundary action -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Legendre
variable {K : Type*} [Field K] [CharZero K]

lemma old_symmetric : oldH.transpose = oldH := by decide +kernel
lemma new_symmetric : newH.transpose = newH := by decide +kernel

omit [CharZero K] in
lemma cast_symmetric (M : Matrix (Fin 40) (Fin 40) ℚ) (h : M.transpose = M) :
    (castMatrix M : Matrix (Fin 40) (Fin 40) K).IsSymm := by
  ext i j
  exact congrArg (fun q : ℚ => (q : K)) (congrFun (congrFun h i) j)

omit [CharZero K] in
lemma pair_comm (u v : Point K) : pair u v = pair v u := dotProduct_comm _ _

omit [CharZero K] in
lemma background_pair (u : Point K) :
    pair (fun i => (background i : K)) u = u 22 + u 29 + u 36 := by
  norm_num [pair, background, dotProduct, Fin.sum_univ_succ]
  ring

lemma cut_matrix (u v : Point K) : cutAction u v =
    matrixAction u v + pair (fun i => (background i : K)) (u - v) := by
  rw [cutAction, source_matrix, linear_cell_formula, background_pair]
  simp only [Pi.sub_apply]
  ring

omit [CharZero K] in
lemma bilinear_variation (M : Matrix (Fin 40) (Fin 40) K)
    (u v du dv : Point K) (e : K) :
    pair (u + e • du) (M.mulVec (v + e • dv)) =
      pair u (M.mulVec v) + e * (pair du (M.mulVec v) + pair u (M.mulVec dv)) +
        e ^ 2 * pair du (M.mulVec dv) := by
  simp only [pair, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma variation (u v du dv : Point K) (e : K) :
    cutAction (u + e • du) (v + e • dv) = cutAction u v +
      e * (pair (post u v) dv - pair (pre u v) du) + e ^ 2 * matrixAction du dv := by
  have ho := cast_symmetric (K := K) oldH old_symmetric
  have hn := cast_symmetric (K := K) newH new_symmetric
  have hs0 : pair u ((castMatrix oldH).mulVec du) =
      pair du ((castMatrix oldH).mulVec u) := ho.dotProduct_mulVec_comm
  have hs1 : pair v ((castMatrix newH).mulVec dv) =
      pair dv ((castMatrix newH).mulVec v) := hn.dotProduct_mulVec_comm
  have ht : pair ((castMatrix mixed).transpose.mulVec u) dv =
      pair u ((castMatrix mixed).mulVec dv) := by
    rw [pair_comm]
    exact Matrix.dotProduct_transpose_mulVec _ _ _
  simp only [cut_matrix, matrixAction, bilinear_variation, hs0, hs1]
  simp only [pre, post, pair, add_dotProduct, sub_dotProduct, neg_dotProduct,
    dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  change _ = _
  dsimp [pair] at ht
  rw [ht]
  rw [dotProduct_comm ((castMatrix newH).mulVec v) dv,
    dotProduct_comm ((castMatrix oldH).mulVec u) du,
    dotProduct_comm ((castMatrix mixed).mulVec v) du]
  ring

lemma real_directional_derivative (u v du dv : Point ℝ) :
    HasDerivAt (fun e : ℝ => cutAction (u + e • du) (v + e • dv))
      (pair (post u v) dv - pair (pre u v) du) 0 := by
  have he : (fun e : ℝ => cutAction (u + e • du) (v + e • dv)) =
      fun e : ℝ => cutAction u v + e * (pair (post u v) dv - pair (pre u v) du) +
        e ^ 2 * matrixAction du dv := by
    funext e
    exact variation u v du dv e
  rw [he]
  convert ((hasDerivAt_const (0 : ℝ) (cutAction u v)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (pair (post u v) dv - pair (pre u v) du))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (matrixAction du dv)) using 1 <;> simp
  all_goals rfl

end Artform.Scores.NonabelianGravity.Legendre
