import ArtformScores.GravityBridge.Native.NativeDetailTests.RetuningStatements

/-! # One coarse scalar rescaling fails two original stationary tests -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



open CurvedSubdivision

lemma original_two_heldout_stationary_values :
    stationaryValue 1 (5 / 4) (3 / 4) < -(45 / 32 : ℝ) ∧
      -(80 / 27 : ℝ) < stationaryValue 1 (5 / 3) (4 / 3) := by
  have hD1 := (actual_detail_root_budget (5 / 4) (3 / 4) (by norm_num) (by norm_num) (by
    norm_num)).1
  have hD2 := (actual_detail_root_budget (5 / 3) (4 / 3) (by norm_num) (by norm_num) (by
    norm_num)).1
  have hr1 : (Real.sqrt (detailD (5 / 4) (3 / 4))) ^ 2 = 23332 / 10201 := by
    rw [Real.sq_sqrt hD1.le]
    norm_num [detailD, detailA, detailB]
  have hr2 : (Real.sqrt (detailD (5 / 3) (4 / 3))) ^ 2 = 660953 / 91809 := by
    rw [Real.sq_sqrt hD2.le]
    norm_num [detailD, detailA, detailB]
  have hn1 := Real.sqrt_nonneg (detailD (5 / 4) (3 / 4))
  have hn2 := Real.sqrt_nonneg (detailD (5 / 3) (4 / 3))
  unfold stationaryValue
  constructor <;> nlinarith

lemma no_constant_coarse_curvature_rescaling :
    ¬ ∃ beta : ℝ,
      stationaryValue 1 (5 / 4) (3 / 4) = -beta * (15 / 8) ∧
      stationaryValue 1 (5 / 3) (4 / 3) = -beta * (40 / 9) := by
  rintro ⟨beta, h1, h2⟩
  have h := original_two_heldout_stationary_values
  rw [h1] at h
  rw [h2] at h
  linarith [h.1, h.2]

lemma actual_two_heldout_proper_boosts :
    (5 / 4 : ℚ) ^ 2 - (3 / 4) ^ 2 = 1 ∧ (5 / 3 : ℚ) ^ 2 - (4 / 3) ^ 2 = 1 ∧
    (17 / 8 : ℚ) ^ 2 - (15 / 8) ^ 2 = 1 ∧ (41 / 9 : ℚ) ^ 2 - (40 / 9) ^ 2 = 1 := by norm_num

/-- **GAC2:native-coarse-scalar-retuning**
(one coarse scalar rescaling fails two original stationary tests). -/
@[ledger "GAC2:native-coarse-scalar-retuning"]
theorem retuningLaw : Statement.retuningLaw := by
  exact ⟨original_two_heldout_stationary_values,
    no_constant_coarse_curvature_rescaling,
    actual_two_heldout_proper_boosts⟩

/-! ## Non-vacuity -/
example : 0 < (3 / 4 : ℝ) ∧ 0 < (4 / 3 : ℝ) := by norm_num

end Artform.Scores.GravityBridge.Native.NativeDetailTests
