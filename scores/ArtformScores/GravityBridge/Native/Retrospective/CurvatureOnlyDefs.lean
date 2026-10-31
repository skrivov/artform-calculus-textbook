import ArtformScores.GravityBridge.Native.Retrospective.PolynomialInverse
import ArtformScores.GravityBridge.Native.Preparation

/-! # Curvature-only elimination fails the original signed force -/

namespace Artform.Scores.GravityBridge.Native.Retrospective

open Matrix



def curvatureOnlyPreparation (t z : ℚ) : Fin 3 → ℚ := (2 * t) • connectionSource z

def spectralPreparation (t z : ℚ) : Fin 3 → ℚ := (2 * t / (1 + 2 * t)) • connectionSource z

def paramCompleteAction (t z : ℚ) (c : Fin 3 → ℚ) : ℚ :=
  -2 * t * z ^ 2 + dotProduct c (paramConnection t *ᵥ c) / 2 +
    2 * t * dotProduct c (connectionSource z)

end Artform.Scores.GravityBridge.Native.Retrospective
