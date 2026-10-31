import ArtformScores.GravityBridge.QuantumNoiseDefs

/-! # Uncertainty form noise and a symplectic dilation pilot -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:uncertainty-noise** (uncertainty form noise and a symplectic dilation pilot). -/
@[ledger "GAC:uncertainty-noise"]
def quantumNoiseLaw : Prop :=
  (∀ (y c : ℝ) (z : Fin 2 → ℂ),
    uncertaintyValue y c z = (y + c) / 2 * Complex.normSq (z 0 + Complex.I * z 1) +
      (y - c) / 2 * Complex.normSq (z 0 - Complex.I * z 1)) ∧
  (∀ y c : ℝ, (∀ z : Fin 2 → ℂ, 0 ≤ uncertaintyValue y c z) ↔ |c| ≤ y) ∧
  (∀ r t : ℝ, r ^ 2 + t ^ 2 = 1 → ∀ x y : TwoModes,
    twoModeArea (beamSplitter r t x) (beamSplitter r t y) = twoModeArea x y) ∧
  (∀ eta y : ℝ, eta ≤ 1 →
    ((∀ z : Fin 2 → ℂ, 0 ≤ uncertaintyValue y ((1 - eta) / 2) z) ↔ (1 - eta) / 2 ≤ y)) ∧
  (∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
    (Real.sqrt eta) ^ 2 = eta ∧ (Real.sqrt (1 - eta)) ^ 2 = 1 - eta ∧
    (Real.sqrt eta) ^ 2 + (Real.sqrt (1 - eta)) ^ 2 = 1) ∧
  (∀ r t v : ℝ, r ^ 2 * v + t ^ 2 * (1 / 2) = r ^ 2 * v + t ^ 2 / 2) ∧
  (¬ Function.Injective (fun x : TwoModes =>
    (beamSplitter (Real.sqrt 2 / 2) (Real.sqrt 2 / 2) x).1))

end Artform.Scores.GravityBridge.Statement
