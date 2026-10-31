import ArtformScores.GravityBridge.LoopDefs

/-! # Finite Gaussian loop with an explicit analytic error -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:finite-gaussian-loop** (finite gaussian loop with an explicit analytic error). -/
@[ledger "GAC:finite-gaussian-loop"]
def loopLaw : Prop :=
  (∀ A B s : ℝ, 0 < B → 0 < A * B - s ^ 2 →
    MeasureTheory.Integrable (loopGaussianBlock A B s) ∧
    (∫ x : ℝ × ℝ, loopGaussianBlock A B s x) =
      Real.sqrt (Real.pi / loopSchur A B s) * Real.sqrt (Real.pi / (B / 2))) ∧
  (∀ A B s : ℝ, 0 < A → 0 < B → 0 < A * B - s ^ 2 →
    Real.log ((∫ x : ℝ × ℝ, loopGaussianBlock A B s x) /
      (∫ x : ℝ × ℝ, loopGaussianBlock A B 0 x)) =
      -(1 / 2) * Real.log (1 - s ^ 2 / (A * B))) ∧
  (∀ (I : Type*) [Fintype I] (A B : I → ℝ) (s : ℝ),
    (∀ i, 0 < B i) → (∀ i, 0 < A i * B i - s ^ 2) →
    MeasureTheory.Integrable
      (fun x : I → ℝ × ℝ => ∏ i, loopGaussianBlock (A i) (B i) s (x i)) ∧
    finiteLoopPartition A B s =
      ∏ i, (Real.sqrt (Real.pi / loopSchur (A i) (B i) s) *
        Real.sqrt (Real.pi / (B i / 2)))) ∧
  (∀ (I : Type*) [Fintype I] (A B : I → ℝ) (s : ℝ),
    (∀ i, 0 < A i) → (∀ i, 0 < B i) → (∀ i, 0 < A i * B i - s ^ 2) →
    Real.log (finiteLoopPartition A B s / finiteLoopPartition A B 0) =
      -(1 / 2) * ∑ i, Real.log (1 - s ^ 2 / (A i * B i))) ∧
  (∀ (I : Type*) [Fintype I] (w : I → ℝ), (∀ i, 1 ≤ w i) →
    ∀ theta : ℝ, 0 ≤ theta → theta ≤ 1 / 2 →
    |finiteLoopFreeEnergy w theta + theta / 2 * ∑ i, 1 / w i| ≤
      Fintype.card I * theta ^ 2) ∧
  (∀ (i : Fin 4) (s : ℝ), s ^ 2 ≤ 1 / 2 →
    regulatorFreeEnergy i s = finiteLoopFreeEnergy (fun r => (pairWeight i r : ℝ)) (s ^ 2)) ∧
  (∀ (i : Fin 4) (s : ℝ), s ^ 2 ≤ 1 / 2 →
    |regulatorFreeEnergy i s - regulatorLoopCoefficient i * s ^ 2| ≤ 8 * s ^ 4) ∧
  (regulatorLoopCoefficient 0 = -19 / 40 ∧ regulatorLoopCoefficient 1 = -17 / 30 ∧
    regulatorLoopCoefficient 0 - regulatorLoopCoefficient 1 = 11 / 120)

end Artform.Scores.GravityBridge.Statement
