import ArtformScores.GravityBridge.Native.Retrospective.PolynomialInverseDefs

/-! # The original signed block through a quadratic matrix relation -/

namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement

open Matrix

/-- **GAC2:signed-block-polynomial-inverse**
(the original signed block through a quadratic matrix relation). -/
@[ledger "GAC2:signed-block-polynomial-inverse"]
def polynomialInverseLaw : Prop :=
  
    (curvatureBlock * curvatureBlock =
    curvatureBlock + (2 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ)) ∧
    (torsionBlock.transpose * facePairing * torsionBlock =
    -(curvatureBlock + (2 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ))) ∧
    (∀ (t : ℚ),
    paramConnection t = (1 - 2 * t) • curvatureBlock - (4 * t) • 1) ∧
    (∀ (t : ℚ),
    paramConnection t * inverseNumerator t = inverseDenominator t • 1) ∧
    (∀ (t : ℚ),
    inverseNumerator t * paramConnection t = inverseDenominator t • 1) ∧
    (∀ (t : ℚ) (_hp : 1 - 4 * t ≠ 0) (_hm : 1 + 2 * t ≠ 0),
    inverseDenominator t ≠ 0) ∧
    (∀ (t : ℚ) (_hp : 1 - 4 * t ≠ 0) (_hm : 1 + 2 * t ≠ 0),
    paramConnection t * polynomialInverse t = 1 ∧
    polynomialInverse t * paramConnection t = 1) ∧
    (paramConnection kappa = connectionBlock) ∧
    (polynomialInverse kappa =
    (1 / 19982 : ℚ) • ((9999 : ℚ) • curvatureBlock - (9595 : ℚ) • 1)) ∧
    (∀ (t : ℚ) (_hp : 1 - 4 * t ≠ 0) (_hm : 1 + 2 * t ≠ 0),
    (paramConnection t)⁻¹ = polynomialInverse t) ∧
    (connectionBlock⁻¹ = polynomialInverse kappa)

end Artform.Scores.GravityBridge.Native.Retrospective.Statement
