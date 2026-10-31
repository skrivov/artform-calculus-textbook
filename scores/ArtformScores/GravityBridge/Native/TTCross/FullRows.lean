import ArtformScores.GravityBridge.Native.TTCross.FullRowsStatements

/-! # Embed the actual paired source in all four coordinate rows -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

open Matrix CoordinateSymbol
lemma original_column_coefficients (j a : K) (hj : j ^ 2 = -1) :
    (fun r => nativeUpperCoefficients j ![a, -a, 0] r *ᵥ ![0, 0, 0, 1]) =
      fun r => rowCoefficients a r • ![0, 0, 0, 1] := by
  let g := nativeUpperCoefficients j ![a, -a, 0]
  have hev (z : K) :
      g 0 *ᵥ ![0, 0, 0, 1] + z • (g 1 *ᵥ ![0, 0, 0, 1]) + z ^ 2 • (g 2 *ᵥ ![0, 0, 0, 1]) +
        z ^ 3 • (g 3 *ᵥ ![0, 0, 0, 1]) + z ^ 4 • (g 4 *ᵥ ![0, 0, 0, 1]) =
        (-(1 / 101 : K) * (9999 / 9991) * a ^ 2 * (z ^ 2 - 2 * a ^ 2) * (z ^ 2 + a ^ 2)) • ![0,
          0, 0, 1] := by
    rw [← Matrix.smul_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
      ← Matrix.add_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec]
    change matrixPolynomial (nativeUpperCoefficients j ![a, -a, 0]) z *ᵥ ![0, 0, 0, 1] = _
    rw [← complete_native_quartic j z ![a, -a, 0] hj]
    exact paired_axis_native_column j z a hj
  ext r b
  have h0 := congrFun (hev 0) b
  have h1 := congrFun (hev 1) b
  have hm1 := congrFun (hev (-1)) b
  have h2 := congrFun (hev 2) b
  have hm2 := congrFun (hev (-2)) b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1 hm1 h2 hm2
  fin_cases r <;> change (g _ *ᵥ (![0, 0, 0, 1] : Vec4 (K := K))) b = _
  · norm_num [rowCoefficients] at *
    linear_combination h0
  · norm_num [rowCoefficients]
    linear_combination (2 / 3 : K) * h1 - (2 / 3 : K) * hm1 - (1 / 12 : K) * h2 + (1 / 12 : K) * hm2
  · norm_num [rowCoefficients]
    linear_combination (2 / 3 : K) * h1 + (2 / 3 : K) * hm1 - (1 / 24 : K) * h2 - (1 / 24 : K) *
      hm2 - (5 / 4 : K) * h0
  · norm_num [rowCoefficients]
    linear_combination -(1 / 6 : K) * h1 + (1 / 6 : K) * hm1 + (1 / 12 : K) * h2 - (1 / 12 : K)
      * hm2
  · norm_num [rowCoefficients]
    linear_combination -(1 / 6 : K) * h1 - (1 / 6 : K) * hm1 + (1 / 24 : K) * h2 + (1 / 24 : K)
      * hm2 + (1 / 4 : K) * h0

omit [CharZero K] in
lemma literal_eta_last (c : K) : (etaMatrix (K := K)) *ᵥ (c • ![0, 0, 0, 1]) = c • ![0, 0, 0, 1]
  := by
  ext i
  fin_cases i <;> norm_num [etaMatrix, signature, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma original_four_row_identity (j a : K) (hj : j ^ 2 = -1) (x : Fin 5 → K) :
    fullCoordinateRow j a x = (-(1 / 101 : K) * (9999 / 9991) * a ^ 2 * scalarRow a x) • ![0, 0,
      0, 1] := by
  unfold fullCoordinateRow
  have he : (etaMatrix (K := K)) *ᵥ ![0, 0, 0, 1] = ![0, 0, 0, 1] := by
    simpa only [one_smul] using literal_eta_last (1 : K)
  simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_smul, he]
  simp_rw [congrFun (original_column_coefficients j a hj)]
  simp only [literal_eta_last]
  ext i
  fin_cases i <;> norm_num [literal_eta_last, etaMatrix, signature, Matrix.mulVec,
    rowCoefficients, scalarRow, dotProduct, Fin.sum_univ_succ]
  ring

lemma complete_forced_column_residual (j a v : K) (hj : j ^ 2 = -1) (x : Fin 5 → K) :
    fullCoordinateRow j a x + actualCrossSource a v =
      (-(1 / 101 : K) * (9999 / 9991) * a ^ 2 * (scalarRow a x + 2 * a ^ 2 * v)) • ![0, 0, 0, 1]
        := by
  rw [original_four_row_identity j a hj]
  ext i
  fin_cases i <;> norm_num [actualCrossSource]
  ring

lemma actual_full_column_solution (j a v : K) (hj : j ^ 2 = -1) (x : Fin 5 → K)
    (hx : scalarRow a x = -2 * a ^ 2 * v) : fullCoordinateRow j a x + actualCrossSource a v = 0
      := by
  rw [complete_forced_column_residual j a v hj x, hx]
  simp

/-- **GAC2:native-four-row-source-embedding**
(embed the actual paired source in all four coordinate rows). -/
@[ledger "GAC2:native-four-row-source-embedding"]
theorem fullRowsLaw : Statement.fullRowsLaw := by
  intro K _ _
  exact ⟨original_column_coefficients,
    original_four_row_identity,
    complete_forced_column_residual,
    actual_full_column_solution⟩

/-! ## Non-vacuity -/
example : actualCrossSource (1 : ℚ) 1 3 = -198 / 9991 := by norm_num [actualCrossSource]
example : fullCoordinateRow Complex.I (1 : ℂ) ![-1 / 2, 0, 1, 0, -2] +
    actualCrossSource (1 : ℂ) 1 = 0 := by
  apply actual_full_column_solution Complex.I 1 1 Complex.I_sq
  norm_num [scalarRow]

end Artform.Scores.GravityBridge.Native.TTCross
