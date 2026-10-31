import ArtformScores.GravityBridge.Regulator
import ArtformScores.GravityBridge.Gaussian

/-! # Declared finite Gaussian background-field partition and response -/

namespace Artform.Scores.GravityBridge

noncomputable section

def loopGaussianBlock (A B s : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.exp (-(A * x.1 ^ 2 + 2 * s * x.1 * x.2 + B * x.2 ^ 2) / 2)

def loopSchur (A B s : ℝ) : ℝ := A / 2 - (s / 2) ^ 2 / (B / 2)

def finiteLoopPartition {I : Type*} [Fintype I] (A B : I → ℝ) (s : ℝ) : ℝ :=
  ∫ x : I → ℝ × ℝ, ∏ i, loopGaussianBlock (A i) (B i) s (x i)

def finiteLoopFreeEnergy {I : Type*} [Fintype I] (w : I → ℝ) (theta : ℝ) : ℝ :=
  (1 / 2) * ∑ i, Real.log (1 - theta / w i)

def regulatorA (i : Fin 4) (r : AxisRepresentatives i) : ℝ := modePrecision 2 1 r.val

def regulatorB (i : Fin 4) (r : AxisRepresentatives i) : ℝ :=
  modePrecision 2 1 (r.val ^^^ momentumAxis i)

def regulatorFreeEnergy (i : Fin 4) (s : ℝ) : ℝ :=
  -Real.log (finiteLoopPartition (regulatorA i) (regulatorB i) s /
    finiteLoopPartition (regulatorA i) (regulatorB i) 0)

def regulatorLoopCoefficient (i : Fin 4) : ℝ := -(loopResponse 2 1 i : ℚ) / 4

end

end Artform.Scores.GravityBridge
