import ArtformScores.GravityBridge.PhaseStatements

/-! # The finite quadratic loop keeps a measurable relative reference phase -/

namespace Artform.Scores.GravityBridge

noncomputable section

open Matrix


lemma sqrt_two_normalization : Real.sqrt (2 : ℝ) / 2 = (Real.sqrt 2)⁻¹ := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  apply (mul_right_injective₀ hn)
  change Real.sqrt 2 * (Real.sqrt 2 / 2) = Real.sqrt 2 * (Real.sqrt 2)⁻¹
  rw [mul_inv_cancel₀ hn]
  nlinarith

lemma sqrt_two_complex_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

lemma sqrt_two_complex_cube : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℝ) := by
  rw [pow_succ, sqrt_two_complex_sq]

lemma binary_phase_loop : (binaryFourier * binaryChirp) ^ 3 = binaryGaussPhase • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [binaryFourier, binaryChirp, binaryGaussPhase, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring_nf <;> simp [Complex.I_sq, sqrt_two_complex_cube] <;> ring

lemma binary_classical_loop : (classicalFourier * classicalChirp) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [classicalFourier, classicalChirp, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals decide +kernel

lemma binary_phase_not_one : binaryGaussPhase ≠ 1 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [binaryGaussPhase] at hi

lemma binary_gauss_sum :
    ((Real.sqrt 2 : ℝ) / 2 : ℂ) * (∑ x : Fin 2, Complex.I ^ (x.val ^ 2)) = binaryGaussPhase := by
  norm_num [Fin.sum_univ_two, binaryGaussPhase]

lemma binary_interference : Complex.normSq (1 + binaryGaussPhase) = 2 + Real.sqrt 2 := by
  have hr : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  norm_num [binaryGaussPhase, Complex.normSq_apply]
  nlinarith

lemma binary_fourier_unitary : binaryFourier.conjTranspose * binaryFourier = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [binaryFourier, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [sqrt_two_complex_sq, map_ofNat]

lemma binary_chirp_unitary : binaryChirp.conjTranspose * binaryChirp = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [binaryChirp, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]

lemma binary_fourier_weyl :
    binaryFourier * binaryX * binaryFourier.conjTranspose = binaryZ ∧
    binaryFourier * binaryZ * binaryFourier.conjTranspose = binaryX := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [binaryFourier, binaryX, binaryZ, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [sqrt_two_complex_sq, map_ofNat]

lemma binary_chirp_weyl :
    binaryChirp * binaryX * binaryChirp.conjTranspose = Complex.I • (binaryX * binaryZ) ∧
    binaryChirp * binaryZ * binaryChirp.conjTranspose = binaryZ := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [binaryChirp, binaryX, binaryZ, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

lemma binary_phase_norm : Complex.normSq binaryGaussPhase = 1 := by
  have hr : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  norm_num [binaryGaussPhase, Complex.normSq_apply]
  nlinarith

lemma binary_interference_not_trivial : Complex.normSq (1 + binaryGaussPhase) ≠ 4 := by
  rw [binary_interference]
  have hr : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- **GAC:finite-gaussian-phase** (actual finite Gauss phase and projective classical endpoint). -/
@[ledger "GAC:finite-gaussian-phase"]
theorem phaseLaw : Statement.phaseLaw := by
  exact ⟨binary_fourier_unitary, binary_chirp_unitary, binary_fourier_weyl,
    binary_chirp_weyl, binary_classical_loop, binary_phase_loop, binary_gauss_sum,
    binary_phase_norm, binary_phase_not_one, binary_interference, binary_interference_not_trivial⟩

/-! ## Non-vacuity -/

example : ((binaryFourier * binaryChirp) ^ 3) 0 0 = binaryGaussPhase := by
  rw [binary_phase_loop]
  simp

end

end Artform.Scores.GravityBridge
