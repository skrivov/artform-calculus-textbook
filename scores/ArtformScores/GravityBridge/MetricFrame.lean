import ArtformScores.GravityBridge.MetricFrameStatements
/-! # Metric jets and independent frame connection data -/
namespace Artform.Scores.GravityBridge
noncomputable section
lemma finite_lorentz_same_metric :
    (∀ i j, metricFromFrame finiteLorentzFrame i j =
      metricFromFrame (1 : Matrix (Fin 4) (Fin 4) ℚ) i j) ∧
    finiteLorentzFrame.det = 1 ∧ finiteLorentzFrame 0 1 = 4 / 3 := by
  decide +kernel
lemma lorentz_metric_kernel (b r : Fin 3 → ℚ) :
    ∀ i j, coframeMetricVariation (lorentzGenerator b r) i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coframeMetricVariation, lorentzGenerator, nativeEta]
lemma metric_kernel_parametrization (F : Matrix (Fin 4) (Fin 4) ℚ) :
    (∀ i j, coframeMetricVariation F i j = 0) ↔
      ∃ b r : Fin 3 → ℚ, F = lorentzGenerator b r := by
  constructor
  · intro h
    refine ⟨![F 0 1, F 0 2, F 0 3], ![F 3 2, F 1 3, F 2 1], ?_⟩
    ext i j
    have he := h i j
    fin_cases i <;> fin_cases j <;>
      norm_num [coframeMetricVariation, lorentzGenerator, nativeEta] at he ⊢ <;> linarith
  · rintro ⟨b, r, rfl⟩
    exact lorentz_metric_kernel b r
lemma lorentz_parameters_injective :
    Function.Injective (fun br : (Fin 3 → ℚ) × (Fin 3 → ℚ) => lorentzGenerator br.1 br.2) := by
  intro x y h
  apply Prod.ext
  · funext i
    fin_cases i
    · exact congrFun (congrFun h 0) 1
    · exact congrFun (congrFun h 0) 2
    · exact congrFun (congrFun h 0) 3
  · funext i
    fin_cases i
    · exact congrFun (congrFun h 3) 2
    · exact congrFun (congrFun h 1) 3
    · exact congrFun (congrFun h 2) 1
lemma metric_kernel_jet_parametrization (N : ℕ)
    (F : Fin N → Matrix (Fin 4) (Fin 4) ℚ) :
    (∀ n i j, coframeMetricVariation (F n) i j = 0) ↔
      ∃ b r : Fin N → Fin 3 → ℚ, ∀ n, F n = lorentzGenerator (b n) (r n) := by
  classical
  constructor
  · intro h
    choose b r hb using fun n => (metric_kernel_parametrization (F n)).mp (h n)
    exact ⟨b, r, hb⟩
  · rintro ⟨b, r, h⟩ n i j
    rw [h n]
    exact lorentz_metric_kernel _ _ i j
lemma pure_frame_torsion_curvature (k : Fin 4 → ℚ) (F : Matrix (Fin 4) (Fin 4) ℚ) :
    (∀ i j a, linearTorsionSymbol k F (pureFrameConnection k F) i j a = 0) ∧
    (∀ i j a b, linearCurvatureSymbol k (pureFrameConnection k F) i j a b = 0) := by
  constructor
  · intro i j a
    dsimp [linearTorsionSymbol, pureFrameConnection]
    ring
  · intro i j a b
    dsimp [linearCurvatureSymbol, pureFrameConnection]
    ring
lemma pure_connection_lorentz (k : Fin 4 → ℚ) (b r : Fin 3 → ℚ) (i a c : Fin 4) :
    coframeMetricVariation (pureFrameConnection k (lorentzGenerator b r) i) a c = 0 := by
  calc
    _ = k i * coframeMetricVariation (lorentzGenerator b r) a c := by
      dsimp [coframeMetricVariation, pureFrameConnection]
      ring
    _ = 0 := by rw [lorentz_metric_kernel, mul_zero]
/-- **GAC:metric-frame-kinematics** (metric jets and independent frame connection data). -/
@[ledger "GAC:metric-frame-kinematics"]
theorem metricFrameLaw : Statement.metricFrameLaw := by
  exact ⟨finite_lorentz_same_metric,
    lorentz_metric_kernel,
    metric_kernel_parametrization,
    lorentz_parameters_injective,
    metric_kernel_jet_parametrization,
    pure_frame_torsion_curvature,
    pure_connection_lorentz⟩
/-! ## Non-vacuity -/
example : (∀ i j, coframeMetricVariation (lorentzGenerator ![1, 0, 0] 0) i j = 0) ∧
    lorentzGenerator ![1, 0, 0] 0 0 1 = 1 ∧
    pureFrameConnection ![1, 0, 0, 0] (lorentzGenerator ![1, 0, 0] 0) 0 0 1 = 1 := by
  refine ⟨lorentz_metric_kernel _ _, ?_, ?_⟩ <;>
    norm_num [lorentzGenerator, pureFrameConnection]
end
end Artform.Scores.GravityBridge
