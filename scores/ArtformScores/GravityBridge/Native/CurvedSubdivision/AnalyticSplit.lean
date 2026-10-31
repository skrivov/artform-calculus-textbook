import ArtformScores.GravityBridge.Native.CurvedSubdivision.CoreBoost
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Supporting original curved subdivision algebra -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40
noncomputable section

def nativeSplitAction (b u r j : ℝ) : ℝ :=
  -b * (Real.sinh (u + r) + Real.sinh (u - r)) - (1 / 101 : ℝ) * b * (Real.cosh (u + r) - 1) - j * r

def nativeSplitFirst (b u r j : ℝ) : ℝ :=
  -b * (Real.cosh (u + r) - Real.cosh (u - r)) - (1 / 101 : ℝ) * b * Real.sinh (u + r) - j

def nativeSplitSecond (b u r : ℝ) : ℝ :=
  -b * (Real.sinh (u + r) + Real.sinh (u - r)) - (1 / 101 : ℝ) * b * Real.cosh (u + r)

lemma actual_split_first_derivative (b u r j : ℝ) :
    HasDerivAt (fun t => nativeSplitAction b u t j) (nativeSplitFirst b u r j) r := by
  have hp := (hasDerivAt_id r).const_add u
  have hm := (hasDerivAt_const r u).sub (hasDerivAt_id r)
  have h := ((((Real.hasDerivAt_sinh (u + r)).comp r hp).add
    ((Real.hasDerivAt_sinh (u - r)).comp r hm)).const_mul (-b)).sub
      ((((Real.hasDerivAt_cosh (u + r)).comp r hp).sub_const 1).const_mul ((1 / 101 : ℝ) * b))
  convert h.sub ((hasDerivAt_id r).const_mul j) using 1
  · rfl
  · dsimp [nativeSplitFirst, Function.comp_def]
    ring

lemma actual_split_second_derivative (b u r j : ℝ) :
    HasDerivAt (fun t => nativeSplitFirst b u t j) (nativeSplitSecond b u r) r := by
  have hp := (hasDerivAt_id r).const_add u
  have hm := (hasDerivAt_const r u).sub (hasDerivAt_id r)
  have h := ((((Real.hasDerivAt_cosh (u + r)).comp r hp).sub
    ((Real.hasDerivAt_cosh (u - r)).comp r hm)).const_mul (-b)).sub
      (((Real.hasDerivAt_sinh (u + r)).comp r hp).const_mul ((1 / 101 : ℝ) * b))
  convert h.sub_const j using 1
  · rfl
  · dsimp [nativeSplitSecond, Function.comp_def]
    ring

lemma old_symmetric_detail_not_stationary (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    nativeSplitFirst b u 0 0 ≠ 0 := by
  norm_num [nativeSplitFirst]
  exact ⟨ne_of_gt hb, ne_of_gt hu⟩

lemma source_repairs_detail_exactly (b u j : ℝ) :
    nativeSplitFirst b u 0 j = 0 ↔ j = -(1 / 101 : ℝ) * b * Real.sinh u := by
  norm_num [nativeSplitFirst]
  constructor <;> intro h <;> linarith

lemma repaired_detail_Hessian_nonzero (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    nativeSplitSecond b u 0 < 0 := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  have hbs := mul_pos hb hs
  have hbc := mul_pos hb hc
  simp only [nativeSplitSecond, add_zero, sub_zero]
  nlinarith

/-! ## Non-vacuity -/
example : nativeSplitFirst 1 (Real.log 2) 0 0 ≠ 0 := by
  exact old_symmetric_detail_not_stationary 1 (Real.log 2) (by norm_num)
    (Real.log_pos (by norm_num))
end
end Artform.Scores.GravityBridge.Native.CurvedSubdivision
