import ArtformScores.GravityBridge.Native.CoordinateSymbol.ExceptionalStatements

/-! # R7 band and R8 angular exceptional domains -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix



open Matrix
noncomputable section

lemma angular_numerator_factor (k : Fin 3 → ℝ) :
    radiusSquared k * spatialFourth k - cubicMoment k ^ 2 = angularSquares k := by
  unfold radiusSquared spatialFourth cubicMoment angularSquares
  ring

lemma angular_psi_factor (k : Fin 3 → ℝ) (hR : radiusSquared k ≠ 0) :
    radiusSquared k * angularPsi k = angularSquares k := by
  unfold angularPsi
  field_simp
  exact angular_numerator_factor k

lemma angular_nonnegative (k : Fin 3 → ℝ) : 0 ≤ angularSquares k := by
  unfold angularSquares
  positivity

lemma angular_zero_strata (k : Fin 3 → ℝ) (hR : radiusSquared k ≠ 0) :
    angularPsi k = 0 ↔
      (k 0 = 0 ∨ k 1 = 0 ∨ k 0 = k 1) ∧
      (k 0 = 0 ∨ k 2 = 0 ∨ k 0 = k 2) ∧
      (k 1 = 0 ∨ k 2 = 0 ∨ k 1 = k 2) := by
  have h0 : 0 ≤ k 0 ^ 2 * k 1 ^ 2 * (k 0 - k 1) ^ 2 := by positivity
  have h1 : 0 ≤ k 0 ^ 2 * k 2 ^ 2 * (k 0 - k 2) ^ 2 := by positivity
  have h2 : 0 ≤ k 1 ^ 2 * k 2 ^ 2 * (k 1 - k 2) ^ 2 := by positivity
  rw [← mul_eq_zero_iff_left hR, angular_psi_factor k hR]
  unfold angularSquares
  constructor
  · intro h
    have h01 : k 0 ^ 2 * k 1 ^ 2 * (k 0 - k 1) ^ 2 = 0 := by linarith
    have h02 : k 0 ^ 2 * k 2 ^ 2 * (k 0 - k 2) ^ 2 = 0 := by linarith
    have h12 : k 1 ^ 2 * k 2 ^ 2 * (k 1 - k 2) ^ 2 = 0 := by linarith
    simpa only [mul_eq_zero, sq_eq_zero_iff,
      sub_eq_zero, or_assoc] using And.intro h01 (And.intro h02 h12)
  · rintro ⟨h01, h02, h12⟩
    have h01' : k 0 ^ 2 * k 1 ^ 2 * (k 0 - k 1) ^ 2 = 0 := by
      rcases h01 with h|h|h <;> simp [h]
    have h02' : k 0 ^ 2 * k 2 ^ 2 * (k 0 - k 2) ^ 2 = 0 := by
      rcases h02 with h|h|h <;> simp [h]
    have h12' : k 1 ^ 2 * k 2 ^ 2 * (k 1 - k 2) ^ 2 = 0 := by
      rcases h12 with h|h|h <;> simp [h]
    rw [h01', h02', h12']; norm_num

lemma same_band_different_R8_strata :
    fixedBand ![3, 3, 0] ∧ fixedBand ![3, -3, 0] ∧
    angularPsi ![3, 3, 0] = 0 ∧ angularPsi ![3, -3, 0] = 162 := by
  norm_num [fixedBand, radiusSquared, angularPsi, spatialFourth, cubicMoment, Fin.forall_fin_succ]

/-- **GAC2:native-angular-exceptional-domains**
(r7 band and r8 angular exceptional domains). -/
@[ledger "GAC2:native-angular-exceptional-domains"]
theorem exceptionalLaw : Statement.exceptionalLaw := by
  exact ⟨angular_numerator_factor,
    angular_psi_factor,
    angular_nonnegative,
    angular_zero_strata,
    same_band_different_R8_strata⟩

/-! ## Non-vacuity -/
example : fixedBand ![3, 3, 0] ∧ angularPsi ![3, 3, 0] = 0 :=
  ⟨same_band_different_R8_strata.1, same_band_different_R8_strata.2.2.1⟩
end

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
