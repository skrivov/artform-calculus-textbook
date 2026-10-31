import ArtformScores.GravityBridge.Native.TTCross.ZeroResponseStatements

/-! # Source-driven response with all four zero initial coordinate jets -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40



noncomputable section

lemma actual_forced_derivatives (a l t : ℝ) :
    HasDerivAt (fun s => zeroPreparedJet a l s 0) (zeroPreparedJet a l t 1) t ∧
    HasDerivAt (fun s => zeroPreparedJet a l s 1) (zeroPreparedJet a l t 2) t ∧
    HasDerivAt (fun s => zeroPreparedJet a l s 2) (zeroPreparedJet a l t 3) t ∧
    HasDerivAt (fun s => zeroPreparedJet a l s 3) (zeroPreparedJet a l t 4) t := by
  have hc := (Real.hasDerivAt_cos (l * t)).comp t ((hasDerivAt_id t).const_mul l)
  have hs := (Real.hasDerivAt_sin (l * t)).comp t ((hasDerivAt_id t).const_mul l)
  have ha := (Real.hasDerivAt_cos (a * t)).comp t ((hasDerivAt_id t).const_mul a)
  have hb := (Real.hasDerivAt_sin (a * t)).comp t ((hasDerivAt_id t).const_mul a)
  have hh := (Real.hasDerivAt_cosh (l * t)).comp t ((hasDerivAt_id t).const_mul l)
  have hi := (Real.hasDerivAt_sinh (l * t)).comp t ((hasDerivAt_id t).const_mul l)
  constructor
  · convert (((hc.const_mul (-3)).sub hh).add (ha.const_mul 4)).div_const (6 * a ^ 2) using 1
    · rfl
    · dsimp [zeroPreparedJet, Function.comp_def];ring
  constructor
  · convert (((hs.const_mul (3 * l)).sub (hi.const_mul l)).sub
      (hb.const_mul (4 * a))).div_const (6 * a ^ 2) using 1
    · rfl
    · dsimp [zeroPreparedJet, Function.comp_def];ring
  constructor
  · convert (((hc.const_mul (3 * l ^ 2)).sub (hh.const_mul (l ^ 2))).sub
      (ha.const_mul (4 * a ^ 2))).div_const (6 * a ^ 2) using 1
    · rfl
    · dsimp [zeroPreparedJet, Function.comp_def];ring
  · convert (((hs.const_mul (-3 * l ^ 3)).sub (hi.const_mul (l ^ 3))).add
      (hb.const_mul (4 * a ^ 3))).div_const (6 * a ^ 2) using 1
    · rfl
    · dsimp [zeroPreparedJet, Function.comp_def];ring

lemma actual_forced_zero_jets (a l : ℝ) (hl : l ^ 2 = 2 * a ^ 2) :
    zeroPreparedJet a l 0 0 = 0 ∧ zeroPreparedJet a l 0 1 = 0 ∧
    zeroPreparedJet a l 0 2 = 0 ∧ zeroPreparedJet a l 0 3 = 0 := by
  norm_num [zeroPreparedJet, hl]
  left
  ring

lemma actual_TT_forced_row (a l t : ℝ) (ha : a ≠ 0) (hl : l ^ 2 = 2 * a ^ 2) :
    zeroPreparedJet a l t 4 - a ^ 2 * zeroPreparedJet a l t 2-
      2 * a ^ 4 * zeroPreparedJet a l t 0 = -2 * a ^ 2 * Real.cos (l * t) := by
  have hl4 : l ^ 4 = 4 * a ^ 4 := by nlinarith [sq_nonneg (l ^ 2 - 2 * a ^ 2)]
  norm_num [zeroPreparedJet, hl, hl4]
  field_simp
  ring

lemma growing_coefficient_retained (a l t : ℝ) (ha : a ≠ 0) :
    zeroPreparedJet a l t 0 =
      (-3 * Real.cos (l * t) + 4 * Real.cos (a * t)) / (6 * a ^ 2) - Real.cosh (l * t) / (6 * a
        ^ 2) ∧
      -(1 / (6 * a ^ 2)) ≠ 0 := by
  constructor
  · simp only [zeroPreparedJet, Matrix.cons_val_zero];ring
  · exact neg_ne_zero.mpr (one_div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)))

/-- **GAC2:native-tt-zero-preparation-response**
(source-driven response with all four zero initial coordinate jets). -/
@[ledger "GAC2:native-tt-zero-preparation-response"]
theorem zeroResponseLaw : Statement.zeroResponseLaw := by
  exact ⟨actual_forced_derivatives,
    actual_forced_zero_jets,
    actual_TT_forced_row,
    growing_coefficient_retained⟩

/-! ## Non-vacuity -/
example : zeroPreparedJet 1 (Real.sqrt 2) 0 4 = -2 := by
  have h : (Real.sqrt 2) ^ 4 = 4 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num [zeroPreparedJet, h]
end

end Artform.Scores.GravityBridge.Native.TTCross
