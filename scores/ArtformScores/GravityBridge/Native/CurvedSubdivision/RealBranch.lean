import ArtformScores.GravityBridge.Native.CurvedSubdivision.Normal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Supporting original curved subdivision algebra -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40
noncomputable section

def stationaryC (c s : ℝ) : ℝ := detailA c s / Real.sqrt (detailD c s)
def stationaryS (c s : ℝ) : ℝ := -detailB s / Real.sqrt (detailD c s)
def stationaryValue (b c s : ℝ) : ℝ := (1 / 101 : ℝ) * b - b * Real.sqrt (detailD c s)

lemma actual_detail_strict_gap (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (hco : 1 < c) (hs : 0 < s) :
    (1 / 101 : ℝ) ^ 2 < detailD c s := by
  rw [original_detail_discriminant c s hc]
  have hc0 : 0 < c := by linarith
  have hsc := mul_pos hs hc0
  nlinarith [sq_nonneg s]

lemma actual_detail_root_budget (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (hco : 1 < c) (hs : 0 < s) :
    0 < detailD c s ∧ (1 / 101 : ℝ) < Real.sqrt (detailD c s) := by
  have hg := actual_detail_strict_gap c s hc hco hs
  have hd : 0 < detailD c s := by linarith
  refine ⟨hd, ?_⟩
  have hr := Real.sqrt_nonneg (detailD c s)
  have he := Real.sq_sqrt hd.le
  nlinarith

lemma actual_stationary_proper_boost (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (hco : 1 < c) (hs : 0 < s) :
    0 < stationaryC c s ∧ (stationaryC c s) ^ 2 - (stationaryS c s) ^ 2 = 1 := by
  have hd := (actual_detail_root_budget c s hc hco hs).1
  have hr : 0 < Real.sqrt (detailD c s) := Real.sqrt_pos.mpr hd
  have hr2 := Real.sq_sqrt hd.le
  constructor
  · unfold stationaryC detailA
    positivity
  · unfold stationaryC stationaryS
    field_simp
    rw [hr2]
    simp [detailD]

lemma actual_stationary_current_return (b c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1)
    (hco : 1 < c) (hs : 0 < s) :
    currentDetailForce b c s (stationaryC c s) (stationaryS c s) 0 = 0 ∧
    currentDetailHessian b c s (stationaryC c s) (stationaryS c s) =
      -b * Real.sqrt (detailD c s) ∧
    currentFineValue b c s (stationaryC c s) (stationaryS c s) = stationaryValue b c s := by
  have hd := (actual_detail_root_budget c s hc hco hs).1
  have hr : Real.sqrt (detailD c s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hr2 := Real.sq_sqrt hd.le
  have hp : detailA c s * stationaryC c s + detailB s * stationaryS c s =
      Real.sqrt (detailD c s) := by
    unfold stationaryC stationaryS
    field_simp
    rw [hr2]
    unfold detailD
    ring
  constructor
  · unfold currentDetailForce stationaryC stationaryS
    ring
  constructor
  · unfold currentDetailHessian
    rw [hp]
  · unfold currentFineValue stationaryValue
    rw [hp]

lemma stationary_coframe_covector_nonzero (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1)
    (hco : 1 < c) (hs : 0 < s) :
    (1 / 101 : ℝ) - Real.sqrt (detailD c s) < 0 := by
  have := (actual_detail_root_budget c s hc hco hs).2
  linarith

lemma stationary_merge_exact_defect (b c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1)
    (hco : 1 < c) (hs : 0 < s) :
    (stationaryValue b c s + 2 * b * c * s) *
      ((1 / 101 : ℝ) + 2 * c * s + Real.sqrt (detailD c s)) = 4 * b * s ^ 4 := by
  have hd := (actual_detail_root_budget c s hc hco hs).1
  have hr2 := Real.sq_sqrt hd.le
  have hD := original_detail_discriminant c s hc
  unfold stationaryValue
  linear_combination -b * hr2 - b * hD + (4 * b * s ^ 2) * hc

lemma stationary_merge_strict_defect (b c s : ℝ) (hb : 0 < b) (hc : c ^ 2 - s ^ 2 = 1)
    (hco : 1 < c) (hs : 0 < s) : 0 < stationaryValue b c s + 2 * b * c * s := by
  have he := stationary_merge_exact_defect b c s hc hco hs
  have hden : 0 < (1 / 101 : ℝ) + 2 * c * s + Real.sqrt (detailD c s) := by positivity
  have hpos : 0 < (4 : ℝ) * b * s ^ 4 := by positivity
  nlinarith

/-! ## Non-vacuity -/
example : (1 / 101 : ℝ) < Real.sqrt (detailD (5 / 4) (3 / 4)) ∧
    0 < stationaryValue 1 (5 / 4) (3 / 4) + 2 * 1 * (5 / 4) * (3 / 4) :=
  ⟨(actual_detail_root_budget (5 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num)).2,
    stationary_merge_strict_defect 1 (5 / 4) (3 / 4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)⟩
end
end Artform.Scores.GravityBridge.Native.CurvedSubdivision
