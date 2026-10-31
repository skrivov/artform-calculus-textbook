import ArtformScores.GravityBridge.Native.NativeDetailTests.WindowStatements

/-! # Exact native source window for both child rapidities -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal



open CurvedSubdivision

lemma actual_detail_endpoint_sources (b u : ℝ) :
    nativeSplitFirst b u (-u) 0 = 2 * b * (Real.sinh u) ^ 2 ∧
    nativeSplitFirst b u u 0 = -2 * b * (Real.sinh u) ^ 2 - (2 / 101 : ℝ) * b * Real.sinh u *
      Real.cosh u := by
  have hc := Real.cosh_sq_sub_sinh_sq u
  have hm : u- -u = 2 * u := by ring
  constructor
  · rw [nativeSplitFirst, hm, add_neg_cancel, Real.cosh_zero, Real.sinh_zero, Real.cosh_two_mul]
    linear_combination b * hc
  · rw [nativeSplitFirst, sub_self, show u + u = 2 * u by ring, Real.cosh_zero,
      Real.cosh_two_mul, Real.sinh_two_mul]
    linear_combination -b * hc

lemma actual_stationary_source_window (b u r j : ℝ) (hb : 0 < b) (hu : 0 < u)
    (hz : nativeSplitFirst b u r j = 0) :
    (-u < r ∧ r < u) ↔
      (-2 * b * (Real.sinh u) ^ 2 - (2 / 101 : ℝ) * b * Real.sinh u * Real.cosh u < j ∧
        j < 2 * b * (Real.sinh u) ^ 2) := by
  have hj : j = nativeSplitFirst b u r 0 := by
    unfold nativeSplitFirst at hz ⊢
    linarith
  rw [hj, ← (actual_detail_endpoint_sources b u).1, ← (actual_detail_endpoint_sources b u).2]
  have ha := native_detail_force_strictAnti b u 0 hb hu
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨ha hr, ha hl⟩
  · rintro ⟨hl, hr⟩
    constructor
    · by_contra h
      have hm := ha.antitone (le_of_not_gt h)
      linarith
    · by_contra h
      have hm := ha.antitone (le_of_not_gt h)
      linarith

lemma bounded_child_rapidities_from_source_window (b u j : ℝ) (hb : 0 < b) (hu : 0 < u)
    (hj : -2 * b * (Real.sinh u) ^ 2 - (2 / 101 : ℝ) * b * Real.sinh u * Real.cosh u < j ∧
      j < 2 * b * (Real.sinh u) ^ 2) :
    ∃ r : ℝ, nativeSplitFirst b u r j = 0 ∧
      0 < u + r ∧ u + r < 2 * u ∧ 0 < u - r ∧ u - r < 2 * u := by
  obtain ⟨r, hr, _⟩ := every_real_source_has_unique_native_detail b u j hb hu
  have hw := (actual_stationary_source_window b u r j hb hu hr).mpr hj
  exact ⟨r, hr, by linarith, by linarith, by linarith, by linarith⟩

/-- **GAC2:native-source-rapidity-window**
(exact native source window for both child rapidities). -/
@[ledger "GAC2:native-source-rapidity-window"]
theorem windowLaw : Statement.windowLaw := by
  exact ⟨actual_detail_endpoint_sources,
    actual_stationary_source_window,
    bounded_child_rapidities_from_source_window⟩

/-! ## Non-vacuity -/
example : ∃ r : ℝ, nativeSplitFirst 1 (Real.log 2) r 0 = 0 ∧
    0 < Real.log 2 + r ∧ Real.log 2 + r < 2 * Real.log 2 ∧
    0 < Real.log 2 - r ∧ Real.log 2 - r < 2 * Real.log 2 := by
  have hu : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply bounded_child_rapidities_from_source_window 1 (Real.log 2) 0 (by norm_num) hu
  have hs := Real.sinh_pos_iff.mpr hu
  have hc := Real.cosh_pos (Real.log 2)
  constructor <;> nlinarith [mul_pos hs hc, sq_pos_of_pos hs]

end Artform.Scores.GravityBridge.Native.NativeDetailTests
