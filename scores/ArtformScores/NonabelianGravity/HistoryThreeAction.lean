import ArtformScores.NonabelianGravity.HistoryAction

/-! # Exact three-cell absolute action, affine endpoints and both sources -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
open Legendre

def threeAction (x z : Point ℚ) (j y : Vector 2) : ℚ :=
  cutAction x (row y 0) + cutAction (row y 0) (row y 1) +
    cutAction (row y 1) z - pair (row j 0) (row y 0) - pair (row j 1) (row y 1)

lemma sum_two (v : Vector 2) :
    ∑ t : Fin 2, ∑ i : Fin 40, v (t, i) =
      (∑ i : Fin 40, v (0, i)) + ∑ i : Fin 40, v (1, i) := by
  simp [Fin.sum_univ_succ]

lemma pair_rows (v w : Vector 2) : dotProduct v w =
    pair (row v 0) (row w 0) + pair (row v 1) (row w 1) := by
  simp only [dotProduct, Fintype.sum_prod_type]
  exact sum_two (fun ti => v ti * w ti)

lemma history_row_zero (y : Vector 2) :
    row ((historyMatrix 2).mulVec y) 0 =
      middleH.mulVec (row y 0) + mixed.mulVec (row y 1) := by
  funext i
  rw [row, matrix_row]
  simp

lemma history_row_one (y : Vector 2) :
    row ((historyMatrix 2).mulVec y) 1 =
      middleH.mulVec (row y 1) + mixed.transpose.mulVec (row y 0) := by
  funext i
  rw [row, matrix_row]
  simp

lemma residual_row_zero (x z : Point ℚ) (j : Vector 2) :
    row (sourceResidual x z j) 0 = row j 0 - mixed.transpose.mulVec x := by
  funext i
  simp [row, sourceResidual]

lemma residual_row_one (x z : Point ℚ) (j : Vector 2) :
    row (sourceResidual x z j) 1 = row j 1 - mixed.mulVec z := by
  funext i
  simp [row, sourceResidual]

lemma three_action_decomposition (x z : Point ℚ) (j y : Vector 2) :
    threeAction x z j y = endpointAction x z +
      quadraticAction (H := historyMatrix 2) (sourceResidual x z j) y := by
  simp only [threeAction, quadraticAction, pair_rows, history_row_zero,
    history_row_one, residual_row_zero, residual_row_one, endpointAction,
    cut_matrix, matrixAction, castMatrix_rat, middleH, Matrix.add_mulVec,
    pair, dotProduct_add, sub_dotProduct, dotProduct_sub, Rat.cast_id]
  have ht₀ := transpose_pair mixed x (row y 0)
  have ht₁ := Matrix.dotProduct_transpose_mulVec mixed (row y 1) (row y 0)
  have hz := pair_comm (row y 1) (mixed.mulVec z)
  dsimp [pair] at ht₀ ht₁ hz
  rw [ht₀, ht₁, hz]
  ring

lemma three_stationary_action (c : Certificate (historyMatrix 2))
    (x z : Point ℚ) (j free : Vector 2) (h : Compatible c (sourceResidual x z j)) :
    threeAction x z j (solution c (sourceResidual x z j) free) =
      endpointAction x z - (1 / 2 : ℚ) * sourceContact c (sourceResidual x z j) := by
  rw [three_action_decomposition, stationary_quadratic c _ _ h]
  ring

end Artform.Scores.NonabelianGravity.HistoryElimination
