import ArtformScores.GravityBridge.Native.CoordinateSymbol.Inverse
import ArtformScores.GravityBridge.Native.R7Blocks.Repair

/-! # Compact reflected native band and both light-cone inverse guards -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix



def radiusSquared (k : Fin 3 → ℝ) : ℝ := k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2

def cubicMoment (k : Fin 3 → ℝ) : ℝ := k 0 ^ 3 + k 1 ^ 3 + k 2 ^ 3

def fixedBand (k : Fin 3 → ℝ) : Prop :=
  9 ≤ radiusSquared k ∧ radiusSquared k ≤ 25 ∧ ∀ i, (k i) ^ 2 ≤ (81 / 100 : ℝ) * radiusSquared k

noncomputable def lightConeDiscriminant (σ ρ : ℝ) (k : Fin 3 → ℝ) : ℝ :=
  -(cubicMoment k - σ * ρ ^ 3) ^ 2 / 4

def lightConeMomentum (σ ρ : ℝ) (k : Fin 3 → ℝ) : Vec4 (K := ℝ) :=
  ![σ * ρ, k 0, k 1, k 2]

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
