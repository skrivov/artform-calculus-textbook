import ArtformScores.NonabelianGravity.LegendreSchur
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Finite source tests for explicitly naive quantum boundary kernels

The identities concern the fixed native Taylor cut action. They select no
physical measure, convergent integral or quantization prescription.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.BoundaryQuantum
open Artform.Scores.NonabelianGravity.Legendre

noncomputable def outputDirection : Point ℝ := fun i => if i = 25 then 1 else 0
noncomputable def negativeDirection : Point ℝ :=
  fun i => if i = 25 ∨ i = 32 ∨ i = 39 then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Check the entire new endpoint Hessian on a genuinely nonzero flat direction.
lemma new_output_zero : (castMatrix newH).mulVec outputDirection = 0 := by
  funext i
  rw [newH_product]
  fin_cases i <;> norm_num [newHProduct, outputDirection]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The full mixed block also has this output column zero.
lemma mixed_output_zero : (castMatrix mixed).mulVec outputDirection = 0 := by
  funext i
  rw [mixed_product]
  fin_cases i <;> norm_num [mixedProduct, outputDirection]

lemma output_nonzero : outputDirection ≠ 0 := by
  intro h
  have h25 := congrFun h 25
  norm_num [outputDirection] at h25

lemma action_output_flat (u v : Point ℝ) (t : ℝ) :
    cutAction u (v + t • outputDirection) = cutAction u v := by
  have hn : pair outputDirection ((castMatrix newH).mulVec v) =
      pair v ((castMatrix newH).mulVec outputDirection) :=
    (cast_symmetric (K := ℝ) newH new_symmetric).dotProduct_mulVec_comm
  have hp : pair outputDirection ((castMatrix newH).mulVec v) = 0 := by
    rw [hn, new_output_zero]
    exact dotProduct_zero v
  simp only [cutAction, linear_cell_formula, source_matrix, matrixAction,
    Matrix.mulVec_add, Matrix.mulVec_smul, new_output_zero, mixed_output_zero,
    smul_zero, add_zero]
  simp only [pair, add_dotProduct, smul_dotProduct] at hp ⊢
  simp [outputDirection, hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Expand the original action on the rotational diagonal ray, keeping all terms.
lemma negative_ray (t : ℝ) :
    cutAction (t • negativeDirection) 0 = -(291 / 101 : ℝ) * t ^ 2 := by
  simp only [cutAction, linear_cell_formula, source_matrix, matrixAction]
  simp only [pair, dotProduct]
  simp_rw [oldH_product, newH_product, mixed_product]
  norm_num [pair, dotProduct, Fin.sum_univ_succ, oldHProduct, newHProduct,
    mixedProduct, negativeDirection]
  ring

noncomputable def naivePhaseKernel (ℏ : ℝ) (u v : Point ℝ) : ℂ :=
  Complex.exp (Complex.I * ((cutAction u v : ℝ) : ℂ) / ℏ)

lemma phase_output_flat (ℏ : ℝ) (u v : Point ℝ) (t : ℝ) :
    naivePhaseKernel ℏ u (v + t • outputDirection) = naivePhaseKernel ℏ u v := by
  simp only [naivePhaseKernel, action_output_flat]

end Artform.Scores.NonabelianGravity.BoundaryQuantum
