import ArtformScores.GravityBridge.Native.CurvedSubdivision.AnalyticSplit

/-! # Supporting original curved subdivision algebra -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40
noncomputable section

def nativeDefect (b u : ℝ) : ℝ :=
  b * (Real.sinh (2 * u) - 2 * Real.sinh u) - (1 / 101 : ℝ) * b * (Real.cosh u - 1)
def nativeDefectFirst (b u : ℝ) : ℝ :=
  b * (2 * Real.cosh (2 * u) - 2 * Real.cosh u) - (1 / 101 : ℝ) * b * Real.sinh u

def nativeDefectSecond (b u : ℝ) : ℝ :=
  b * (4 * Real.sinh (2 * u) - 2 * Real.sinh u) - (1 / 101 : ℝ) * b * Real.cosh u

lemma original_total_defect_factor (b u : ℝ) :
    nativeDefect b u = b * (Real.cosh u - 1) * (2 * Real.sinh u - (1 / 101 : ℝ)) := by
  rw [nativeDefect, Real.sinh_two_mul]
  ring

lemma complete_defect_first (b u : ℝ) :
    HasDerivAt (nativeDefect b) (nativeDefectFirst b u) u := by
  have h2 := (Real.hasDerivAt_sinh (2 * u)).comp u ((hasDerivAt_id u).const_mul 2)
  have h1 := Real.hasDerivAt_sinh u
  have hc := Real.hasDerivAt_cosh u
  convert ((h2.sub (h1.const_mul 2)).const_mul b).sub
    ((hc.sub_const 1).const_mul ((1 / 101 : ℝ) * b)) using 1
  · rfl
  · dsimp [nativeDefectFirst, Function.comp_def]
    ring

lemma complete_defect_second (b u : ℝ) :
    HasDerivAt (nativeDefectFirst b) (nativeDefectSecond b u) u := by
  have h2 := (Real.hasDerivAt_cosh (2 * u)).comp u ((hasDerivAt_id u).const_mul 2)
  have h1 := Real.hasDerivAt_cosh u
  have hs := Real.hasDerivAt_sinh u
  convert (((h2.const_mul 2).sub (h1.const_mul 2)).const_mul b).sub
    (hs.const_mul ((1 / 101 : ℝ) * b)) using 1
  · rfl
  · dsimp [nativeDefectSecond, Function.comp_def]
    ring

lemma coframe_and_mixed_defect_contacts (b u db : ℝ) :
    nativeDefect (b + db) u - nativeDefect b u = nativeDefect db u ∧
    nativeDefectFirst (b + db) u - nativeDefectFirst b u = nativeDefectFirst db u := by
  constructor <;> dsimp only [nativeDefect, nativeDefectFirst] <;> ring

lemma missing_torsion_changes_detail (b u : ℝ) :
    nativeSplitFirst b u 0 0 = -(1 / 101 : ℝ) * b * Real.sinh u := by
  norm_num [nativeSplitFirst]

lemma value_equality_not_first_contact (b u : ℝ) (hb : 0 < b)
    (hs : 2 * Real.sinh u = (1 / 101 : ℝ)) (hc : 1 < Real.cosh u) :
    nativeDefect b u = 0 ∧ 0 < nativeDefectFirst b u := by
  constructor
  · rw [original_total_defect_factor, hs]
    ring
  · have hid : nativeDefectFirst b u = 2 * b * Real.cosh u * (Real.cosh u - 1) := by
      rw [nativeDefectFirst, Real.cosh_two_mul]
      linear_combination (b * Real.sinh u) * hs
    rw [hid]
    positivity

/-! ## Non-vacuity -/
example : nativeDefect 1 (Real.log 2) = 301 / 808 := by
  have he : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  rw [original_total_defect_factor]
  norm_num [Real.sinh_eq, Real.cosh_eq, Real.exp_neg, he]
end
end Artform.Scores.GravityBridge.Native.CurvedSubdivision
