import ArtformScores.GravityBridge.Native.NativeCurrent.CoordinatesDefs

/-! # Original metric momentum and velocity current factors -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent.Statement

open Matrix

/-- **GAC2:native-current-coordinate-factors**
(original metric momentum and velocity current factors). -/
@[ledger "GAC2:native-current-coordinate-factors"]
def coordinatesLaw : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V],
    (∀ (x y : Matrix (Fin 3) (Fin 3) ℚ) (a : ℚ),
    tensorDot (a • x) y = a * tensorDot x y) ∧
    (∀ (x y : Matrix (Fin 3) (Fin 3) ℚ) (a : ℚ),
    tensorDot x (a • y) = a * tensorDot x y) ∧
    (∀ (q p r s : Matrix (Fin 3) (Fin 3) ℚ),
    coframeCut ((1 / 2 : ℚ) • q) p ((1 / 2 : ℚ) • r) s = metricMomentumCut q p r s) ∧
    (∀ (q p r s : Matrix (Fin 3) (Fin 3) ℚ),
    metricVelocityCut q ((2 : ℚ) • p) r ((2 : ℚ) • s) = metricMomentumCut q p r s) ∧
    (∀ (B : V →ₗ[K] V →ₗ[K] K)
    (f c g d : V) (h : K),
    B (f - h • c) (g - h • d) = B f g - h * B f d - h * B c g + h ^ 2 * B c d) ∧
    (metricMomentumCut polarization 0 0 polarization = -1 ∧
    metricVelocityCut polarization 0 0 ((2 : ℚ) • polarization) = -1)

end Artform.Scores.GravityBridge.Native.NativeCurrent.Statement
