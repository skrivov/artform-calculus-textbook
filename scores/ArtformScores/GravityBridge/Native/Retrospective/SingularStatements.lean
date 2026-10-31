import ArtformScores.GravityBridge.Native.Retrospective.SingularDefs
/-! # Singular strata and retained source range guards -/
namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement
open Matrix
open Full40
/-- **GAC2:native-singular-source-strata**
(singular strata and retained source range guards). -/
@[ledger "GAC2:native-singular-source-strata"]
def singularLaw : Prop :=
    (paramConnection (1 / 4) *ᵥ ![1, -1, -1] = 0 ∧
      (![1, -1, -1] : Fin 3 → ℚ) ≠ 0) ∧
    (paramConnection (-1 / 2) *ᵥ ![0, -1, 1] = 0 ∧
      (![0, -1, 1] : Fin 3 → ℚ) ≠ 0) ∧
    (∀ b : Fin 4,
    repeatedBlock b 1 *ᵥ ![1, 1, 1] = 0 ∧
      (![1, 1, 1] : Fin 3 → ℚ) ≠ 0) ∧
    (∀ b : Fin 4,
    repeatedBlock b (-1 / 2) *ᵥ ![1, -1, 0] = 0 ∧
      (![1, -1, 0] : Fin 3 → ℚ) ≠ 0) ∧
    (∀ (z : ℚ),
    paramConnection (1 / 4) *ᵥ spectralPreparation (1 / 4) z +
      (2 * (1 / 4 : ℚ)) • connectionSource z = 0) ∧
    (inverseDenominator (1 / 4) = 0 ∧ polynomialInverse (1 / 4) = 0 ∧
      paramConnection (1 / 4) * polynomialInverse (1 / 4) ≠ 1) ∧
    (∀ (r : Fin 3 → ℚ)
    (_h : ∃ a, repeatedBlock 0 1 *ᵥ a = r),
    r 0 + r 1 + r 2 = 0) ∧
    (∀ (r : Fin 3 → ℚ)
    (_h : ∃ a, paramConnection (1 / 4) *ᵥ a = r),
    r 0 - r 1 - r 2 = 0)
end Artform.Scores.GravityBridge.Native.Retrospective.Statement
