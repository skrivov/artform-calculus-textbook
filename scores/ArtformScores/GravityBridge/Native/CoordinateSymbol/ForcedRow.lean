import ArtformScores.GravityBridge.Native.CoordinateSymbol.ForcedRowStatements

/-! # Native unit-row forcing with zero initial four-jet -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix



noncomputable section

lemma forced_row_derivatives (l t : ℝ) :
    HasDerivAt (fun s => forcedRowJet l s 0) (forcedRowJet l t 1) t ∧
    HasDerivAt (fun s => forcedRowJet l s 1) (forcedRowJet l t 2) t ∧
    HasDerivAt (fun s => forcedRowJet l s 2) (forcedRowJet l t 3) t ∧
    HasDerivAt (fun s => forcedRowJet l s 3) (forcedRowJet l t 4) t := by
  have hc := (Real.hasDerivAt_cosh (l * t)).comp t ((hasDerivAt_id t).const_mul l)
  have hs := (Real.hasDerivAt_sinh (l * t)).comp t ((hasDerivAt_id t).const_mul l)
  have ht := Real.hasDerivAt_cos t
  have hu := Real.hasDerivAt_sin t
  constructor
  · convert (((hc.add (ht.const_mul 2)).sub_const 3).const_mul rowUnitScale).div_const 6 using 1
    · rfl
    · dsimp [forcedRowJet, Function.comp_def]
      ring
  constructor
  · convert (((hs.const_mul l).sub (hu.const_mul 2)).const_mul rowUnitScale).div_const 6 using 1
    · rfl
    · dsimp [forcedRowJet, Function.comp_def]
      ring
  constructor
  · convert (((hc.const_mul (l ^ 2)).sub (ht.const_mul 2)).const_mul rowUnitScale).div_const 6
    using 1
    · rfl
    · dsimp [forcedRowJet, Function.comp_def]
      ring
  · convert (((hs.const_mul (l ^ 3)).add (hu.const_mul 2)).const_mul rowUnitScale).div_const 6
    using 1
    · rfl
    · dsimp [forcedRowJet, Function.comp_def]
      ring

lemma forced_row_zero_initial (l : ℝ) (hl : l ^ 2 = 2) :
    forcedRowJet l 0 0 = 0 ∧ forcedRowJet l 0 1 = 0 ∧
    forcedRowJet l 0 2 = 0 ∧ forcedRowJet l 0 3 = 0 := by
  norm_num [forcedRowJet, hl]

lemma native_row_unit_forcing (l t : ℝ) (hl : l ^ 2 = 2) :
    (-(1 / 101 : ℝ) * (9999 / 9991)) *
      (forcedRowJet l t 4 - forcedRowJet l t 2 - 2 * forcedRowJet l t 0) = 1 := by
  have hl4 : l ^ 4 = 4 := by nlinarith [sq_nonneg (l ^ 2 - 2)]
  norm_num [forcedRowJet, rowUnitScale, hl, hl4]
  ring

/-- **GAC2:native-forced-row-zero-four-jet**
(native unit-row forcing with zero initial four-jet). -/
@[ledger "GAC2:native-forced-row-zero-four-jet"]
theorem forcedRowLaw : Statement.forcedRowLaw := by
  exact ⟨forced_row_derivatives,
    forced_row_zero_initial,
    native_row_unit_forcing⟩

/-! ## Non-vacuity -/
example : forcedRowJet (Real.sqrt 2) 0 0 = 0 ∧
    (-(1 / 101 : ℝ) * (9999 / 9991)) * (forcedRowJet (Real.sqrt 2) 1 4-
      forcedRowJet (Real.sqrt 2) 1 2 - 2 * forcedRowJet (Real.sqrt 2) 1 0) = 1 :=
  ⟨(forced_row_zero_initial _ (Real.sq_sqrt (by norm_num))).1,
    native_row_unit_forcing _ _ (Real.sq_sqrt (by norm_num))⟩
end

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
