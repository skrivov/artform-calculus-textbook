import ArtformScores.GravityBridge.Native.Retrospective.CurvatureOnlyDefs

/-! # Curvature-only elimination fails the original signed force -/

namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement

open Matrix

/-- **GAC2:curvature-only-force-residual**
(curvature-only elimination fails the original signed force). -/
@[ledger "GAC2:curvature-only-force-residual"]
def curvatureOnlyLaw : Prop :=
  
    (∀ (z : ℚ),
    curvatureBlock *ᵥ connectionSource z = -connectionSource z) ∧
    (∀ (t z : ℚ),
    paramConnection t *ᵥ connectionSource z = -(1 + 2 * t) • connectionSource z) ∧
    (∀ (t z : ℚ),
    curvatureBlock *ᵥ curvatureOnlyPreparation t z + (2 * t) • connectionSource z = 0) ∧
    (∀ (t z : ℚ),
    paramConnection t *ᵥ curvatureOnlyPreparation t z + (2 * t) • connectionSource z =
      (-4 * t ^ 2) • connectionSource z) ∧
    (∀ (t z : ℚ) (_hm : 1 + 2 * t ≠ 0),
    paramConnection t *ᵥ spectralPreparation t z + (2 * t) • connectionSource z = 0) ∧
    (∀ (z : ℚ),
    spectralPreparation kappa z = connectionPreparation z) ∧
    (∀ (z : ℚ),
    connectionEquation z (curvatureOnlyPreparation kappa z) ↔ z = 0) ∧
    (∀ (z : ℚ) (c : Fin 3 → ℚ),
    paramCompleteAction kappa z c = completeConnectionAction z c) ∧
    (∀ (t z : ℚ) (_hm : 1 + 2 * t ≠ 0),
    paramCompleteAction t z (spectralPreparation t z) = -2 * t * z ^ 2 / (1 + 2 * t)) ∧
    (∀ (t z : ℚ) (_hm : 1 + 2 * t ≠ 0),
    paramCompleteAction t z (curvatureOnlyPreparation t z) -
      paramCompleteAction t z (spectralPreparation t z) =
        -16 * t ^ 4 * z ^ 2 / (1 + 2 * t))

end Artform.Scores.GravityBridge.Native.Retrospective.Statement
