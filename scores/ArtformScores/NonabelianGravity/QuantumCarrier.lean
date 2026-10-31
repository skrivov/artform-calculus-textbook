import ArtformScores.NonabelianGravity.QuantumCarrierSlice

/-! # The fixed native slice represents all original admitted histories -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.QuantumComposition
open HistoryElimination Legendre BoundaryHistory
open Artform.Scores.GravityBridge.Native.Full40

lemma gauge_kernel (w : Biv ℚ) : (historyMatrix 2).mulVec (gauge w) = 0 := by
  have hg0 : row (gauge w) 0 = gaugeFirst w := by funext i; simp [row, gauge]
  have hg1 : row (gauge w) 1 = gaugeSecond w := by funext i; simp [row, gauge]
  funext k
  rcases k with ⟨t, i⟩
  fin_cases t <;> rw [matrix_row]
  · simpa [hg0, hg1] using! congrFun (first_null w) i
  · simpa [hg0, hg1, add_comm] using! congrFun (second_null w) i

lemma project_preserves_equation (q : Whole) :
    (historyMatrix 2).mulVec (project q) = (historyMatrix 2).mulVec q := by
  have htr : mixed.transpose * activeProjector = mixed.transpose := by
    have h := congrArg Matrix.transpose active_mixed
    simpa [Matrix.transpose_mul, projector_symmetric] using h
  have hp (t : Fin 2) : row (project q) t = activeProjector.mulVec (row q t) := rfl
  funext k
  rcases k with ⟨t, i⟩
  fin_cases t <;> simp [matrix_row, hp, Matrix.mulVec_mulVec,
    middle_active_right, mixed_active, htr]

lemma normalize_preserves_equation (q : Whole) :
    (historyMatrix 2).mulVec (normalize q) = (historyMatrix 2).mulVec q := by
  rw [normalize, project_preserves_equation, Matrix.mulVec_sub, gauge_kernel, sub_zero]

lemma slice_equation (y : Reduced) :
    nativeSlice.mulVec y = restrict ((historyMatrix 2).mulVec (embed y)) := by
  funext i
  simp only [nativeSlice, restrict, Matrix.mulVec, dotProduct, embed]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_ite, mul_zero]
  simp

lemma all_rows_preserved (q : Whole) :
    (historyMatrix 2).mulVec (embed (restrict (normalize q))) = (historyMatrix 2).mulVec q := by
  rw [normalized_in_slice, normalize_preserves_equation]

lemma admitted_slice_exists (r : Whole) (hr : ∃ q, (historyMatrix 2).mulVec q = r) :
    ∃ y : Reduced, (historyMatrix 2).mulVec (embed y) = r ∧
      nativeSlice.mulVec y = restrict r := by
  obtain ⟨q, hq⟩ := hr
  refine ⟨restrict (normalize q), ?_, ?_⟩
  · rw [all_rows_preserved, hq]
  · rw [slice_equation, all_rows_preserved, hq]

end Artform.Scores.NonabelianGravity.QuantumComposition
