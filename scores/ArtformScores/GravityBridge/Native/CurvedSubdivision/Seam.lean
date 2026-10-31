import ArtformScores.GravityBridge.Native.CurvedSubdivision.SeamStatements

/-! # A fused coarse link does not fix the fine seam -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40
lemma exact_boost_parameter_read (q : K) : qC q + qS q = q := by
  unfold qC qS
  ring

lemma rational_boost_injective : Function.Injective (rationalBoost (K := K)) := by
  intro q r h
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 0) 1
  change qC q = qC r at h0
  change qS q = qS r at h1
  have := congrArg₂ (fun x y : K => x + y) h0 h1
  simpa only [exact_boost_parameter_read] using this

lemma actual_two_child_boost_fusion (q r : K) (hq : q ≠ 0) (hr : r ≠ 0) :
    rationalBoost q * rationalBoost r = rationalBoost (q * r) := by
  unfold rationalBoost
  rw [actual_two_boost_product]
  congr 1 <;> unfold qC qS <;> field_simp <;> ring

lemma parent_report_does_not_fix_seam (q r : K) (hq : q ≠ 0) (hr : r ≠ 0) (hne : r ≠ 1) :
    coarseLinkReport (q, q) = coarseLinkReport (q * r, q / r) ∧
      fineSeamLink (q, q) ≠ fineSeamLink (q * r, q / r) := by
  constructor
  · unfold coarseLinkReport
    field_simp
  · intro h
    have hx := rational_boost_injective h
    change q = q * r at hx
    have ht : q * 1 = q * r := by simpa using hx
    exact hne (mul_left_cancel₀ hq ht).symm

lemma same_fused_original_boundary (q r : K) (hq : q ≠ 0) (hr : r ≠ 0) :
    rationalBoost q * rationalBoost q = rationalBoost (q * r) * rationalBoost (q / r) := by
  rw [actual_two_child_boost_fusion q q hq hq,
    actual_two_child_boost_fusion (q * r) (q / r) (mul_ne_zero hq hr) (div_ne_zero hq hr)]
  congr 1
  field_simp

/-- **GAC2:native-curved-seam-detail**
(a fused coarse link does not fix the fine seam). -/
@[ledger "GAC2:native-curved-seam-detail"]
theorem seamLaw : Statement.seamLaw := by
  intro K _ _
  exact ⟨exact_boost_parameter_read,
    rational_boost_injective,
    actual_two_child_boost_fusion,
    parent_report_does_not_fix_seam,
    same_fused_original_boundary⟩

/-! ## Non-vacuity -/
example : coarseLinkReport ((101 / 100 : ℚ), (101 / 100)) =
    coarseLinkReport ((101 / 100) * (1001 / 1000), (101 / 100) / (1001 / 1000)) ∧
    fineSeamLink ((101 / 100 : ℚ), (101 / 100)) ≠ 
      fineSeamLink ((101 / 100) * (1001 / 1000), (101 / 100) / (1001 / 1000)) :=
  parent_report_does_not_fix_seam _ _ (by norm_num) (by norm_num) (by norm_num)

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
