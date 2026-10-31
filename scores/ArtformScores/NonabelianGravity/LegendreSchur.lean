import ArtformScores.NonabelianGravity.LegendreGluing

/-! # Complete stationary two-cell action, with the boundary term and source retained -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Legendre

def twoCellAction (x y z j : Point ℚ) : ℚ :=
  cutAction x y + cutAction y z - pair j y

def endpointAction (x z : Point ℚ) : ℚ :=
  (1 / 2 : ℚ) * pair x (oldH.mulVec x) + (1 / 2 : ℚ) * pair z (newH.mulVec z) +
    pair (fun i => background i) (x - z)

def effectiveAction (x z j : Point ℚ) : ℚ :=
  endpointAction x z - (1 / 2 : ℚ) *
    pair (residual x z j) (middleInverse.mulVec (residual x z j))

lemma transpose_pair (M : Matrix (Fin 40) (Fin 40) ℚ) (u v : Point ℚ) :
    pair (M.transpose.mulVec u) v = pair u (M.mulVec v) := by
  rw [pair_comm]
  exact Matrix.dotProduct_transpose_mulVec _ _ _

lemma two_cell_decomposition (x y z j : Point ℚ) : twoCellAction x y z j =
    endpointAction x z + (1 / 2 : ℚ) * pair y (middleH.mulVec y) -
      pair (residual x z j) y := by
  simp only [twoCellAction, endpointAction, cut_matrix, matrixAction, castMatrix_rat,
    residual, middleH, Matrix.add_mulVec, pair, dotProduct_add,
    sub_dotProduct, dotProduct_sub, Rat.cast_id]
  have ht := transpose_pair mixed x y
  have hz := pair_comm y (mixed.mulVec z)
  dsimp [pair] at ht hz
  rw [ht, hz]
  ring

lemma stationary_action (x y z j : Point ℚ) (h : post x y - pre y z = j) :
    twoCellAction x y z j = effectiveAction x z j := by
  have ha : middleH.mulVec y = residual x z j := (matching_iff x y z j).mp h
  obtain ⟨hr, hy⟩ := (middle_solution (residual x z j) y).mp ha
  have hp : pair (residual x z j) y =
      pair (residual x z j) (middleInverse.mulVec (residual x z j)) := by
    calc
      _ = pair (activeProjector.mulVec (residual x z j)) y := by rw [hr]
      _ = pair (residual x z j) (activeProjector.mulVec y) := by
        have ht := transpose_pair activeProjector (residual x z j) y
        rw [projector_symmetric] at ht
        exact ht
      _ = _ := by rw [hy]
  rw [two_cell_decomposition, ha, pair_comm y, hp]
  unfold effectiveAction
  ring

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
-- A nonzero compatible source leaves a nonzero source-contact contribution.
lemma source_contact_witness : effectiveAction 0 0 unit25 = -9595 / 39964 := by
  decide +kernel

end Artform.Scores.NonabelianGravity.Legendre
