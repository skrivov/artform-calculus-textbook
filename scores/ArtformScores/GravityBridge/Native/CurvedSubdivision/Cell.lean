import ArtformScores.GravityBridge.Native.CurvedSubdivision.CellStatements

/-! # Complete current cubical cell law and symmetric merge defect -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Expand the five actual transports and all six original bivector coordinates.
lemma actual_active_face_mean (h b c0 s0 c1 s1 : K) :
    fullOriginalMean h b c0 s0 c1 s1 0 = fiveTermComplement c0 s0 c1 s1 b := by
  ext a
  fin_cases a <;>
    norm_num [fullOriginalMean, fullCornerBivector, fiveTermComplement, complementaryBivector,
      transportedComplement, inheritedCoframe, complementFirst, complementSecond, complementSign,
      faceFirst, faceSecond, reversedEdge, ownedEdge, boost, wedge, basisVector,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
  norm_num [Matrix.one_apply, Fin.succ]

lemma complete_original_curvature_value (h b c0 s0 c1 s1 : K) (h0 : c0 ^ 2 - s0 ^ 2 = 1) :
    fullOriginalCurvature h b c0 s0 c1 s1 = -b * (c0 * s1 - s0 * c1) := by
  unfold fullOriginalCurvature
  simp_rw [congrFun (all_inverse_skew_faces c0 s0 c1 s1 h0)]
  norm_num [Fin.sum_univ_succ, lieCoordinates, internalStar, bivPair, bivSign]
  rw [actual_active_face_mean, original_five_term_average]
  norm_num [complementaryBivector, wedge, basisVector, lie]
  ring

lemma complete_original_cell_value (h b c0 s0 c1 s1 : K) (hh : h ≠ 0) (hb : b ≠ 0)
    (h0 : c0 ^ 2 - s0 ^ 2 = 1) : fullOriginalCell h b c0 s0 c1 s1 =
      -b * (c0 * s1 - s0 * c1) - (2 / 101 : K) * h * b * (c0 - 1) := by
  unfold fullOriginalCell
  rw [complete_original_curvature_value h b c0 s0 c1 s1 h0,
    original_complete_torsion_density h b c0 s0 hh hb h0]
  ring

lemma actual_current_two_cube_defect (b c s : K) (hb : b ≠ 0) (hc : c ^ 2 - s ^ 2 = 1) :
    fullOriginalCell (1 / 2) b 1 0 c s +
      fullOriginalCell (1 / 2) b c s (c ^ 2 + s ^ 2) (2 * c * s)-
      fullOriginalCell 1 b 1 0 (c ^ 2 + s ^ 2) (2 * c * s) =
      b * (c - 1) * (2 * s - (1 / 101 : K)) := by
  rw [complete_original_cell_value (1 / 2) b 1 0 c s (by norm_num) hb (by norm_num),
    complete_original_cell_value (1 / 2) b c s (c ^ 2 + s ^ 2) (2 * c * s) (by norm_num) hb hc,
    complete_original_cell_value 1 b 1 0 (c ^ 2 + s ^ 2) (2 * c * s) (by norm_num) hb (by norm_num)]
  linear_combination -(b * s) * hc

/-- **GAC2:native-current-curved-cell**
(complete current cubical cell law and symmetric merge defect). -/
@[ledger "GAC2:native-current-curved-cell"]
theorem cellLaw : Statement.cellLaw := by
  intro K _ _
  exact ⟨actual_active_face_mean,
    complete_original_curvature_value,
    complete_original_cell_value,
    actual_current_two_cube_defect⟩

/-! ## Non-vacuity -/
example : fullOriginalCell (1 / 2 : ℚ) 1 1 0 (5 / 4) (3 / 4) +
    fullOriginalCell (1 / 2) 1 (5 / 4) (3 / 4) (17 / 8) (15 / 8)-
    fullOriginalCell 1 1 1 0 (17 / 8) (15 / 8) = 301 / 808 := by
  have hc : (5 / 4 : ℚ) ^ 2 - (3 / 4) ^ 2 = 1 := by norm_num
  convert actual_current_two_cube_defect (1 : ℚ) (5 / 4) (3 / 4) (by norm_num) hc using 1 <;>
    norm_num

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
