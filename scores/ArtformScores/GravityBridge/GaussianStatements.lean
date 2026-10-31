import ArtformScores.GravityBridge.GaussianDefs

/-! # Convergent Gaussian Schur data and normalization -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:gaussian-schur-integral** (convergent gaussian schur data and normalization). -/
@[ledger "GAC:gaussian-schur-integral"]
def gaussianLaw : Prop :=
  (∀ a b c j k q z : ℝ, a ≠ 0 →
    gaussianAction a b c j k q z = gaussianEffective a b c j k q +
      a * (z - gaussianCenter a b j q) ^ 2) ∧
  (∀ a b c j k q : ℝ, 0 < a →
    MeasureTheory.Integrable (fun z : ℝ => Real.exp (-gaussianAction a b c j k q z)) ∧
    (∫ z : ℝ, Real.exp (-gaussianAction a b c j k q z)) =
      Real.exp (-gaussianEffective a b c j k q) * Real.sqrt (Real.pi / a)) ∧
  (∀ a b c : ℝ, a ≠ 0 →
    Matrix.det (!![c, b; b, a] : Matrix (Fin 2) (Fin 2) ℝ) = a * (c - b ^ 2 / a)) ∧
  (¬ MeasureTheory.Integrable (fun z : ℝ => Real.exp (-(0 : ℝ) * z ^ 2)))

end Artform.Scores.GravityBridge.Statement
