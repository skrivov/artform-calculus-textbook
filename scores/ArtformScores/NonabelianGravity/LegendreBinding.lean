import ArtformScores.NonabelianGravity.LegendreSource
import ArtformScores.NonabelianGravity.LegendreRows

/-! # Native pre/post covectors and a constrained relation-valued score

The relation is for the complete quadratic Taylor action with its original
linear curvature boundary term. It is not an invertible forty-variable tick.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Legendre
open Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]


def pair (u v : Point K) : K := dotProduct u v

noncomputable def matrixAction (u v : Point K) : K :=
  (1 / 2 : K) * pair u ((castMatrix oldH).mulVec u) +
    pair u ((castMatrix mixed).mulVec v) +
    (1 / 2 : K) * pair v ((castMatrix newH).mulVec v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Bind every integer monomial to all three complete forty-coordinate Hessian blocks.
lemma polynomial_matrix (u v : Point K) :
    polynomial u v = (202 : K) * matrixAction u v := by
  unfold matrixAction pair dotProduct
  simp_rw [oldH_product, mixed_product, newH_product]
  norm_num [polynomial, evaluate, terms, join,
    oldHProduct, mixedProduct, newHProduct, dotProduct, Fin.sum_univ_succ]
  ring

lemma source_matrix (u v : Point K) : cellQuadratic u v = matrixAction u v := by
  have h := (source_polynomial u v).trans (polynomial_matrix u v)
  exact mul_left_cancel₀ (by norm_num : (202 : K) ≠ 0) h

end Artform.Scores.NonabelianGravity.Legendre
