import ArtformScores.GravityBridge.Native.TTCross.ReadoutStatements

/-! # Read inverse and explicit budget on the paired native band slice -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40



noncomputable section

lemma full_prepared_read_inverse (a : ℝ) (u : Fin 2 → ℝ) :
    pairedReadout (preparedJet a u) = u := prepared_jet_read a u

lemma paired_band_nonzero (a : ℝ) (hlo : 9 / 2 ≤ a ^ 2) : a ≠ 0 := by
  intro h
  subst a
  norm_num at hlo

lemma paired_band_preparation_budget (a : ℝ) (u : Fin 2 → ℝ)
    (hlo : 9 / 2 ≤ a ^ 2) (hhi : a ^ 2 ≤ 25 / 2) :
    |preparedJet a u 0| ≤ |u 1| / 9 ∧ |preparedJet a u 3| ≤ 25 * |u 0| := by
  have ha2 : 0 < a ^ 2 := by linarith
  have h0 : |preparedJet a u 0| = |u 1| / (2 * a ^ 2) := by
    simp [preparedJet, abs_div, abs_mul, abs_of_pos ha2]
  have h3 : |preparedJet a u 3| = 2 * a ^ 2 * |u 0| := by
    simp [preparedJet, abs_mul, abs_of_pos ha2]
  rw [h0, h3]
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < 2 * a ^ 2)).2
    nlinarith [abs_nonneg (u 1)]
  · nlinarith [abs_nonneg (u 0)]

lemma discarded_readout_not_full_trace :
    pairedReadout (![1, 0, 0, 0] : Fin 4 → ℝ) = pairedReadout 0 ∧
      (![1, 0, 0, 0] : Fin 4 → ℝ) ≠ 0 := by
  constructor
  · rfl
  · intro h
    have := congrFun h 0
    norm_num at this

/-- **GAC2:paired-band-preparation-readout**
(read inverse and explicit budget on the paired native band slice). -/
@[ledger "GAC2:paired-band-preparation-readout"]
theorem readoutLaw : Statement.readoutLaw := by
  exact ⟨full_prepared_read_inverse,
    paired_band_nonzero,
    paired_band_preparation_budget,
    discarded_readout_not_full_trace⟩

/-! ## Non-vacuity -/
example : |preparedJet (3 : ℝ) ![3, 4] 0| = 2 / 9 ∧ pairedReadout (preparedJet 3 ![3, 4]) = ![3,
  4] := by
  constructor
  · norm_num [preparedJet]
  · exact full_prepared_read_inverse _ _
example : |preparedJet (3 : ℝ) ![3, 4] 0| ≤ 4 / 9 ∧
    |preparedJet (3 : ℝ) ![3, 4] 3| ≤ 75 := by
  convert paired_band_preparation_budget 3 (![3, 4] : Fin 2 → ℝ) (by norm_num) (by norm_num)
    using 1 <;> norm_num
end

end Artform.Scores.GravityBridge.Native.TTCross
