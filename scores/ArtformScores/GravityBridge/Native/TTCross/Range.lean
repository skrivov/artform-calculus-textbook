import ArtformScores.GravityBridge.Native.TTCross.RangeStatements

/-! # Actual TT source range and failure of global preparation bounds -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

open Matrix CoordinateSymbol
lemma actual_source_has_full_last_axis_range (a r : K) (ha : a ≠ 0) :
    actualCrossSource a (sourceVelocity a r) = r • ![0, 0, 0, 1] := by
  ext i
  fin_cases i <;> norm_num [actualCrossSource, sourceVelocity]
  field_simp

lemma actual_source_zero_iff (a v : K) (ha : a ≠ 0) :
    actualCrossSource a v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hh := congrFun h 3
    norm_num [actualCrossSource] at hh
    exact hh.resolve_left ha
  · intro h
    subst v
    simp [actualCrossSource]

lemma cross_polarization_normalization :
    (∑ i : Fin 4, ∑ l : Fin 4, (crossMetric (K := ℚ) i l) ^ 2) = 4 := by
  norm_num [crossMetric, Fin.sum_univ_succ]

lemma actual_unit_velocity_response (a : ℝ) :
    preparedJet a ![0, 1] 0 = -1 / (2 * a ^ 2) := rfl

lemma no_global_zero_frequency_preparation_budget (B : ℝ) (hB : 0 ≤ B) :
    ∃ a : ℝ, a ≠ 0 ∧ B + 1 ≤ |preparedJet a ![0, 1] 0| := by
  let a : ℝ := 1 / (2 * (B + 1))
  have hb : 0 < B + 1 := by linarith
  have ha : 0 < a := by dsimp [a];positivity
  refine ⟨a, ne_of_gt ha, ?_⟩
  have he : |preparedJet a ![0, 1] 0| = 2 * (B + 1) ^ 2 := by
    rw [actual_unit_velocity_response]
    simp only [abs_div, abs_neg, abs_one, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_pow, abs_of_pos ha]
    dsimp [a]
    field_simp
  rw [he]
  nlinarith [sq_nonneg B]

/-- **GAC2:native-tt-source-range-budget**
(actual tt source range and failure of global preparation bounds). -/
@[ledger "GAC2:native-tt-source-range-budget"]
theorem rangeLaw : Statement.rangeLaw := by
  intro K _ _
  exact ⟨actual_source_has_full_last_axis_range,
    actual_source_zero_iff,
    cross_polarization_normalization,
    actual_unit_velocity_response,
    no_global_zero_frequency_preparation_budget⟩

/-! ## Non-vacuity -/
example : actualCrossSource (2 : ℚ) (sourceVelocity 2 3) = 3 • ![0, 0, 0, 1] :=
  actual_source_has_full_last_axis_range _ _ (by norm_num)

end Artform.Scores.GravityBridge.Native.TTCross
