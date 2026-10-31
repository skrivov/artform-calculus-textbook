import ArtformScores.GravityBridge.QuantumNoiseStatements

/-! # Discarding a symplectic environment retains a nonzero uncertainty budget -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma uncertainty_decomposition (y c : ℝ) (z : Fin 2 → ℂ) :
    uncertaintyValue y c z = (y + c) / 2 * Complex.normSq (z 0 + Complex.I * z 1) +
      (y - c) / 2 * Complex.normSq (z 0 - Complex.I * z 1) := by
  simp [uncertaintyValue, uncertaintyMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma uncertainty_noise_iff (y c : ℝ) :
    (∀ z : Fin 2 → ℂ, 0 ≤ uncertaintyValue y c z) ↔ |c| ≤ y := by
  constructor
  · intro h
    have hm := h ![1, Complex.I]
    have hp := h ![1, -Complex.I]
    norm_num [uncertaintyValue, uncertaintyMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at hm hp
    rw [abs_le]
    constructor <;> linarith
  · intro h z
    have hc := abs_le.mp h
    rw [uncertainty_decomposition]
    have hm := Complex.normSq_nonneg (z 0 - Complex.I * z 1)
    have hp := Complex.normSq_nonneg (z 0 + Complex.I * z 1)
    exact add_nonneg (mul_nonneg (by linarith) hp) (mul_nonneg (by linarith) hm)

lemma beam_splitter_pairing (r t : ℝ) (h : r ^ 2 + t ^ 2 = 1) (x y : TwoModes) :
    twoModeArea (beamSplitter r t x) (beamSplitter r t y) = twoModeArea x y := by
  dsimp [twoModeArea, beamSplitter]
  linear_combination
    (x.1.1 * y.1.2 - x.1.2 * y.1.1 + x.2.1 * y.2.2 - x.2.2 * y.2.1) * h

lemma attenuator_noise (eta y : ℝ) (he1 : eta ≤ 1) :
    (∀ z : Fin 2 → ℂ, 0 ≤ uncertaintyValue y ((1 - eta) / 2) z) ↔
      (1 - eta) / 2 ≤ y := by
  rw [uncertainty_noise_iff, abs_of_nonneg (by linarith)]

lemma attenuation_dilation (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    (Real.sqrt eta) ^ 2 = eta ∧ (Real.sqrt (1 - eta)) ^ 2 = 1 - eta ∧
    (Real.sqrt eta) ^ 2 + (Real.sqrt (1 - eta)) ^ 2 = 1 := by
  rw [Real.sq_sqrt h0, Real.sq_sqrt (by linarith)]
  exact ⟨rfl, rfl, by ring⟩

lemma vacuum_output_variance (r t v : ℝ) :
    r ^ 2 * v + t ^ 2 * (1 / 2) = r ^ 2 * v + t ^ 2 / 2 := by ring

lemma beam_discard_not_injective :
    ¬ Function.Injective (fun x : TwoModes => (beamSplitter (Real.sqrt 2 / 2)
      (Real.sqrt 2 / 2) x).1) := by
  intro h
  have he : (beamSplitter (Real.sqrt 2 / 2) (Real.sqrt 2 / 2)
      (((1, 0), (-1, 0)) : TwoModes)).1 =
      (beamSplitter (Real.sqrt 2 / 2) (Real.sqrt 2 / 2) (0 : TwoModes)).1 := by
    simp [beamSplitter]
  have hz := congrArg (fun x : TwoModes => x.1.1) (h he)
  norm_num at hz

/-- **GAC:uncertainty-noise** (form compatibility, without a channel-construction claim). -/
@[ledger "GAC:uncertainty-noise"]
theorem quantumNoiseLaw : Statement.quantumNoiseLaw := by
  exact ⟨uncertainty_decomposition, uncertainty_noise_iff, beam_splitter_pairing,
    attenuator_noise, attenuation_dilation, vacuum_output_variance, beam_discard_not_injective⟩

/-! ## Non-vacuity -/

example : (∀ z : Fin 2 → ℂ, 0 ≤ uncertaintyValue (1 / 4) (1 / 4) z) ∧
    ¬ ∀ z : Fin 2 → ℂ, 0 ≤ uncertaintyValue 0 (1 / 4) z := by
  rw [uncertainty_noise_iff, uncertainty_noise_iff]
  norm_num

example : (Real.sqrt (2 : ℝ) / 2) ^ 2 + (Real.sqrt 2 / 2) ^ 2 = 1 := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

end

end Artform.Scores.GravityBridge
