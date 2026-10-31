import ArtformScores.GravityBridge.MatterStatements

/-! # The proposed scalar density passes explicit chart and source tests -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma scalar_frame_det (N a : ℚ) : (scalarFrame N a).det = N * a ^ 3 := by
  rw [scalarFrame, Matrix.det_diagonal]
  change N * (a * (a * (a * 1))) = N * a ^ 3
  ring

lemma scalar_frame_inverse (N a : ℚ) (hN : N ≠ 0) (ha : a ≠ 0) :
    scalarFrame N a * scalarInverseFrame N a = 1 ∧
    scalarInverseFrame N a * scalarFrame N a = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [scalarFrame, scalarInverseFrame, Matrix.mul_apply, Fin.sum_univ_succ, hN, ha]

lemma scalar_density_geometry (N a coupling phi source : ℚ) (d : Fin 4 → ℚ) :
    clockScalarDensity N a coupling phi source d =
      -coupling / 2 * (scalarFrame N a).det *
        flatScalarKinetic (frameScalarGradient N a d) - source * phi := by
  rw [scalar_frame_det]
  dsimp [clockScalarDensity, flatScalarKinetic, frameScalarGradient]
  simp only [div_pow]
  ring

lemma constant_coframe_scalar (N a coupling phi source : ℚ) (d : Fin 4 → ℚ)
    (hN : N ≠ 0) (ha : a ≠ 0) :
    clockScalarDensity N a coupling phi source d =
      coupling * a ^ 3 / (2 * N) * (d 0) ^ 2 -
      coupling * N * a / 2 * ((d 1) ^ 2 + (d 2) ^ 2 + (d 3) ^ 2) - source * phi := by
  dsimp [clockScalarDensity]
  field_simp
  ring

lemma rational_boost_kinetic (d : Fin 4 → ℚ) :
    flatScalarKinetic (boostScalarGradient d) = flatScalarKinetic d := by
  norm_num [flatScalarKinetic, boostScalarGradient]
  ring

lemma scalar_exact_variation (N a coupling phi source v eps : ℚ) (d e : Fin 4 → ℚ) :
    clockScalarDensity N a coupling (phi + eps * v) source (d + eps • e) =
      clockScalarDensity N a coupling phi source d +
      eps * scalarFirstVariation N a coupling source v d e +
      eps ^ 2 * clockScalarDensity N a coupling 0 0 e := by
  dsimp [clockScalarDensity, scalarFirstVariation]
  ring

lemma flat_scalar_boost_source (coupling phi source : ℚ) (d : Fin 4 → ℚ) :
    clockScalarDensity 1 1 coupling phi source (boostScalarGradient d) =
      clockScalarDensity 1 1 coupling phi source d := by
  dsimp [clockScalarDensity, boostScalarGradient]
  ring

/-- **GAC:scalar-coframe-candidate** (a specified candidate chart and exact local tests). -/
@[ledger "GAC:scalar-coframe-candidate"]
theorem matterLaw : Statement.matterLaw := by
  exact ⟨scalar_frame_det, scalar_frame_inverse, scalar_density_geometry,
    constant_coframe_scalar, rational_boost_kinetic, flat_scalar_boost_source,
    scalar_exact_variation⟩

/-! ## Non-vacuity -/

example : clockScalarDensity 2 3 7 5 11 ![1, 2, 0, 0] = -367 / 4 := by
  norm_num [clockScalarDensity]

example : boostScalarGradient ![1, 0, 0, 0] = ![(5 / 3 : ℚ), 4 / 3, 0, 0] ∧
    flatScalarKinetic (boostScalarGradient ![1, 0, 0, 0]) = -1 := by
  constructor
  · ext i; fin_cases i <;> norm_num [boostScalarGradient]
  · norm_num [flatScalarKinetic, boostScalarGradient]

end

end Artform.Scores.GravityBridge
