import ArtformScores.GravityBridge.Native.CurvedSubdivision.Cell
import ArtformScores.GravityBridge.Native.CurvedSubdivision.AnalyticSplit

/-! # Supporting original curved subdivision algebra -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40
noncomputable section

def literalTwoChildAction (b u r : ℝ) : ℝ :=
  fullOriginalCell (1 / 2) b 1 0 (Real.cosh (u + r)) (Real.sinh (u + r)) +
    fullOriginalCell (1 / 2) b (Real.cosh (u + r)) (Real.sinh (u + r))
      (Real.cosh (2 * u)) (Real.sinh (2 * u))

lemma full_original_split_source_binding (b u r j : ℝ) (hb : b ≠ 0) :
    literalTwoChildAction b u r - j * r = nativeSplitAction b u r j := by
  have hc : (Real.cosh (u + r)) ^ 2 - (Real.sinh (u + r)) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (u + r)
  have hf : Real.cosh (u + r) * Real.sinh (2 * u) - Real.sinh (u + r) * Real.cosh (2 * u) =
      Real.sinh (u - r) := by
    calc
      _ = Real.sinh (2 * u - (u + r)) := by rw [Real.sinh_sub];ring
      _ = Real.sinh (u - r) := by congr 1;ring
  unfold literalTwoChildAction
  rw [complete_original_cell_value (1 / 2) b 1 0 (Real.cosh (u + r)) (Real.sinh (u + r))
      (by norm_num) hb (by norm_num),
    complete_original_cell_value (1 / 2) b (Real.cosh (u + r)) (Real.sinh (u + r))
      (Real.cosh (2 * u)) (Real.sinh (2 * u)) (by norm_num) hb hc, hf]
  unfold nativeSplitAction
  ring

lemma actual_split_source_duty (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    HasDerivAt (literalTwoChildAction b u) (nativeSplitFirst b u 0 0) 0 ∧
      nativeSplitFirst b u 0 0 ≠ 0 := by
  have he : literalTwoChildAction b u = fun r => nativeSplitAction b u r 0 := by
    funext r
    simpa using full_original_split_source_binding b u r 0 (ne_of_gt hb)
  rw [he]
  exact ⟨actual_split_first_derivative b u 0 0, old_symmetric_detail_not_stationary b u hb hu⟩

lemma symmetric_detail_fails_in_arbitrarily_small_rapidity (b delta : ℝ)
    (hb : 0 < b) (hd : 0 < delta) :
    ∃ u : ℝ, 0 < u ∧ u < delta ∧ nativeSplitFirst b u 0 0 ≠ 0 := by
  refine ⟨delta / 2, by positivity, by linarith, ?_⟩
  exact old_symmetric_detail_not_stationary b (delta / 2) hb (by positivity)

/-! ## Non-vacuity -/
example : literalTwoChildAction 1 (Real.log 2) 0 = nativeSplitAction 1 (Real.log 2) 0 0 := by
  simpa using full_original_split_source_binding 1 (Real.log 2) 0 0 (by norm_num)
end
end Artform.Scores.GravityBridge.Native.CurvedSubdivision
