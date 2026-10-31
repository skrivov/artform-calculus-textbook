import ArtformScores.GravityBridge.Native.GreenComposition.DetailIntegralStatements

/-! # Integrate the same source-bearing detail with its measure -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators
open MeasureTheory



noncomputable section

open MeasureTheory

lemma actual_detail_integral (c a b j : ℝ) (hc : 0 < c) :
    Integrable (fun m : ℝ => Real.exp (-sourceAction c a m b j)) ∧
    (∫ m : ℝ, Real.exp (-sourceAction c a m b j)) =
      Real.exp (-sourceEffective c a b j) * Real.sqrt (Real.pi / (2 * c)) := by
  have he : (fun m : ℝ => Real.exp (-sourceAction c a m b j)) =
      fun m => Real.exp (-sourceEffective c a b j) *
        Real.exp (-(2 * c) * (m - sourceMiddle c a b j) ^ 2) := by
    funext m
    rw [source_complete_square c a m b j (ne_of_gt hc)]
    rw [show -(sourceEffective c a b j + 2 * c * (m - sourceMiddle c a b j) ^ 2) =
      -sourceEffective c a b j + (-(2 * c) * (m - sourceMiddle c a b j) ^ 2) by ring, Real.exp_add]
  rw [he]
  constructor
  · exact ((integrable_exp_neg_mul_sq (by positivity : 0 < 2 * c)).comp_sub_right
      (sourceMiddle c a b j)).const_mul _
  · rw [integral_const_mul, integral_sub_right_eq_self
      (fun m : ℝ => Real.exp (-(2 * c) * m ^ 2)) (sourceMiddle c a b j), integral_gaussian]

lemma detail_integration_differs_from_minimum (c a b j : ℝ) (hc : 0 < c)
    (hn : Real.sqrt (Real.pi / (2 * c)) ≠ 1) :
    (∫ m : ℝ, Real.exp (-sourceAction c a m b j)) ≠ Real.exp (-sourceEffective c a b j) := by
  rw [(actual_detail_integral c a b j hc).2]
  intro he
  have hh : Real.sqrt (Real.pi / (2 * c)) = 1 := by
    exact (mul_left_cancel₀ (ne_of_gt (Real.exp_pos _))) (by simpa only [mul_one] using he)
  exact hn hh

lemma original_detail_measure_not_unit : Real.sqrt (Real.pi / (2 * (1 / 101 : ℝ))) ≠ 1 := by
  have hp := Real.pi_gt_three
  have hb : 1 < Real.pi / (2 * (1 / 101 : ℝ)) := by norm_num;linarith
  have hs := Real.sq_sqrt (by positivity : 0 ≤ Real.pi / (2 * (1 / 101 : ℝ)))
  intro he
  rw [he] at hs
  norm_num at hs
  linarith

lemma detail_coordinate_Jacobian (f : ℝ → ℝ) :
    (∫ z : ℝ, f (2 * z)) = (1 / 2 : ℝ) * (∫ m : ℝ, f m) := by
  have he := MeasureTheory.Measure.integral_comp_mul_left f 2
  norm_num [smul_eq_mul] at he
  exact he

/-- **GAC2:two-cell-source-detail-measure**
(integrate the same source-bearing detail with its measure). -/
@[ledger "GAC2:two-cell-source-detail-measure"]
theorem detailIntegralLaw : Statement.detailIntegralLaw := by
  exact ⟨actual_detail_integral,
    detail_integration_differs_from_minimum,
    original_detail_measure_not_unit,
    detail_coordinate_Jacobian⟩

/-! ## Non-vacuity -/
example : Integrable (fun m : ℝ => Real.exp (-sourceAction (1 / 101) 0 m 2 (2 / 101))) :=
  (actual_detail_integral (1 / 101) 0 2 (2 / 101) (by norm_num)).1
end

end Artform.Scores.GravityBridge.Native.GreenComposition
