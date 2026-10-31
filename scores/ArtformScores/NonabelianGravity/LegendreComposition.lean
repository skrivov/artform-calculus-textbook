import ArtformScores.NonabelianGravity.LegendreCompositionData

/-! # Exact source-bound two-cell rank and elimination certificates -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Legendre

set_option maxRecDepth 1000000

-- Complete rational identities include the four inactive coframe coordinates.
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma middle_inverse_right : middleH * middleInverse = activeProjector := by decide +kernel
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma middle_inverse_left : middleInverse * middleH = activeProjector := by decide +kernel
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma middle_active : activeProjector * middleH = middleH := by decide +kernel
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma middle_active_right : middleH * activeProjector = middleH := by decide +kernel
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma mixed_active : mixed * activeProjector = mixed := by decide +kernel
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma active_mixed : activeProjector * mixed = mixed := by decide +kernel
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma active_mixed_transpose : activeProjector * mixed.transpose = mixed.transpose := by
  decide +kernel
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma projector_symmetric : activeProjector.transpose = activeProjector := by decide +kernel
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma inverse_symmetric : middleInverse.transpose = middleInverse := by decide +kernel

set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma mixed_middle_binding : mixed * middleInverse = mixedMiddle := by decide +kernel

set_option maxHeartbeats 20000000 in
-- The intermediate product prevents recomputing its inner sum for every outer entry.
lemma composed_middle_binding : composedMixed = -(mixedMiddle * mixed) := by decide +kernel

lemma composed_binding : composedMixed = -(mixed * middleInverse * mixed) := by
  rw [mixed_middle_binding, composed_middle_binding]
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma composed_factorization : composedMixed = composedLeft * composedRight := by decide +kernel
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma composed_left_inverse : composedLeftInverse * composedLeft = 1 := by decide +kernel
set_option maxHeartbeats 20000000 in
-- Replay every entry of this complete exact rational certificate in the kernel.
lemma composed_right_inverse : composedRight * composedRightInverse = 1 := by decide +kernel

lemma composed_rank : Matrix.rank composedMixed = 18 := by
  apply le_antisymm
  · rw [composed_factorization]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · have h : composedLeftInverse * composedMixed * composedRightInverse =
        (1 : Matrix (Fin 18) (Fin 18) ℚ) := by
      rw [composed_factorization]
      simp only [Matrix.mul_assoc, composed_right_inverse, Matrix.mul_one, composed_left_inverse]
    calc
      18 = Matrix.rank (1 : Matrix (Fin 18) (Fin 18) ℚ) := by simp
      _ = Matrix.rank (composedLeftInverse * composedMixed * composedRightInverse) := by rw [h]
      _ ≤ Matrix.rank (composedLeftInverse * composedMixed) := Matrix.rank_mul_le_left _ _
      _ ≤ Matrix.rank composedMixed := Matrix.rank_mul_le_right _ _

end Artform.Scores.NonabelianGravity.Legendre
