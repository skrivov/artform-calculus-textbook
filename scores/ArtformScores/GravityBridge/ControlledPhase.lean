import ArtformScores.GravityBridge.ControlledPhaseStatements
/-! # Channel equivalence depends on the allowed reference -/
namespace Artform.Scores.GravityBridge
noncomputable section
open Matrix
lemma scalar_phase_channel_identity (gamma : ℂ) (hg : Complex.normSq gamma = 1)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : scalarPhaseChannel gamma A = A := by
  have hp : star gamma * gamma = 1 := by
    simpa [Complex.mul_conj, mul_comm] using congrArg Complex.ofReal hg
  rw [scalarPhaseChannel, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hp, one_smul]
lemma reference_phase_distinct (gamma : ℂ) (hg : gamma ≠ 1) :
    referencePhaseChannel gamma binaryX ≠ binaryX := by
  intro h
  have he := congrFun (congrFun h 1) 0
  norm_num [referencePhaseChannel, referencePhase, binaryX, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two] at he
  exact hg he
lemma reference_phase_unitary (gamma : ℂ) (hg : Complex.normSq gamma = 1) :
    (referencePhase gamma).conjTranspose * referencePhase gamma = 1 := by
  have hp : (starRingEnd ℂ) gamma * gamma = 1 := by
    simpa [Complex.mul_conj, mul_comm] using congrArg Complex.ofReal hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [referencePhase, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, hp]
lemma binary_loop_channel (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (binaryFourier * binaryChirp) ^ 3 * A *
      ((binaryFourier * binaryChirp) ^ 3).conjTranspose = A := by
  rw [binary_phase_loop]
  exact scalar_phase_channel_identity _ binary_phase_norm A
lemma reference_circuit_amplitude (gamma : ℂ) :
    referenceCircuitAmplitude gamma = (1 + gamma) / 2 := by
  norm_num [referenceCircuitAmplitude, binaryFourier, referencePhase,
    Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp only [sqrt_two_complex_sq, map_ofNat]
  ring
lemma binary_reference_probability :
    Complex.normSq ((1 + binaryGaussPhase) / 2) = (2 + Real.sqrt 2) / 4 ∧
    Complex.normSq ((1 + binaryGaussPhase) / 2) ≠ 1 := by
  have he : Complex.normSq ((1 + binaryGaussPhase) / 2) = (2 + Real.sqrt 2) / 4 := by
    rw [Complex.normSq_div, binary_interference]
    norm_num
  refine ⟨he, ?_⟩
  rw [he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith
/-- **GAC:controlled-phase-equivalence** (channel equivalence depends on the allowed reference). -/
@[ledger "GAC:controlled-phase-equivalence"]
theorem controlledPhaseLaw : Statement.controlledPhaseLaw := by
  exact ⟨scalar_phase_channel_identity,
    reference_phase_distinct,
    reference_phase_unitary,
    binary_loop_channel,
    reference_circuit_amplitude,
    binary_reference_probability⟩
/-! ## Non-vacuity -/
example : (∀ A, scalarPhaseChannel binaryGaussPhase A = A) ∧
    referencePhaseChannel binaryGaussPhase binaryX ≠ binaryX :=
  ⟨scalar_phase_channel_identity _ binary_phase_norm,
    reference_phase_distinct _ binary_phase_not_one⟩
end
end Artform.Scores.GravityBridge
