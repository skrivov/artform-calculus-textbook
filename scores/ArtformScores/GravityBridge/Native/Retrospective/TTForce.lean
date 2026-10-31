import ArtformScores.GravityBridge.Native.Retrospective.TTForceStatements
/-! # The original lower temporal forcing through repeated-factor cancellation -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
open Matrix
open Matrix
lemma repeated_factor_cancels (t R L : ℚ) (ht : t ≠ 0) (hR : R ≠ 0)
    (ha : 1 + 2 * t ≠ 0) (hb : 1 - t ≠ 0) :
    -temporalForceCoefficient t R L / temporalPrincipalCoefficient t R = -t * R * L / 2 := by
  have ha' : 1 + t * 2 ≠ 0 := by simpa only [mul_comm] using ha
  unfold temporalForceCoefficient temporalPrincipalCoefficient repeatedH
  field_simp [ht, hR, ha, hb, ha']
  ring
lemma native_repeated_factor : repeatedH kappa = 10201 / 10300 := by
  norm_num [repeatedH, kappa]
lemma native_temporal_coefficients :
    temporalForceCoefficient kappa (rhoSquared momentum)
      (diagonalContraction momentum polarization) = -63 / 12875 ∧
    -temporalForceCoefficient kappa (rhoSquared momentum)
      (diagonalContraction momentum polarization) /
      temporalPrincipalCoefficient kappa (rhoSquared momentum) = 36 / 505 := by
  norm_num [temporalForceCoefficient, temporalPrincipalCoefficient, repeatedH, kappa,
    rhoSquared, momentum, diagonalContraction, polarization, Fin.sum_univ_succ]
lemma native_temporal_symbol_recovered :
    -temporalForceCoefficient kappa (rhoSquared momentum)
      (diagonalContraction momentum polarization) /
      temporalPrincipalCoefficient kappa (rhoSquared momentum) =
      temporalSymbol momentum polarization := by
  rw [native_temporal_coefficients.2]
  norm_num [temporalSymbol, rhoSquared, momentum, diagonalContraction,
    polarization, Fin.sum_univ_succ]
/-- **GAC2:temporal-forcing-factor-cancellation**
(the original lower temporal forcing through repeated-factor cancellation). -/
@[ledger "GAC2:temporal-forcing-factor-cancellation"]
theorem tTForceLaw : Statement.tTForceLaw := by
  exact ⟨repeated_factor_cancels,
    native_repeated_factor,
    native_temporal_coefficients,
    native_temporal_symbol_recovered⟩
/-! ## Non-vacuity -/
example : temporalPrincipalCoefficient kappa (rhoSquared momentum) ≠ 0 := by
  norm_num [temporalPrincipalCoefficient, repeatedH, kappa, rhoSquared, momentum,
    Fin.sum_univ_succ]
end Artform.Scores.GravityBridge.Native.Retrospective
