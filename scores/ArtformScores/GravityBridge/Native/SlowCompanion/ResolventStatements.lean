import ArtformScores.GravityBridge.Native.SlowCompanion.ResolventDefs

/-! # Guarded resolvent of the complete four-jet companion -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion.Statement

/-- **GAC2:native-companion-resolvent**
(guarded resolvent of the complete four-jet companion). -/
@[ledger "GAC2:native-companion-resolvent"]
def resolventLaw : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V],
    (∀ (g : Fin 5 → Module.End K V) (H : Module.End K V)
    (z : K) (v : V) (b : Fin 4 → V) (_hH : H * g 4 = 1),
    z • resolventState z v b - coordinateStep g H (resolventState z v b) - b =
      ![0, 0, 0, H (coordinatePolynomial g z v - coordinateCauchy g z b)]) ∧
    (∀ (g : Fin 5 → Module.End K V) (H L : Module.End K V)
    (z : K) (b : Fin 4 → V) (_hH : H * g 4 = 1) (_hL : coordinatePolynomial g z * L = 1),
    z • companionResolvent g L z b - coordinateStep g H (companionResolvent g L z b) = b) ∧
    (∀ (g : Fin 5 → Module.End K V) (H : Module.End K V)
    (z : K) (x b : Fin 4 → V)
    (_hres : z • x - coordinateStep g H x = b),
    x = resolventState z (x 0) b) ∧
    (∀ (g : Fin 5 → Module.End K V) (H L : Module.End K V)
    (z : K) (x b : Fin 4 → V) (_hH : H * g 4 = 1) (_hH' : g 4 * H = 1)
    (_hL : L * coordinatePolynomial g z = 1) (_hres : z • x - coordinateStep g H x = b),
    x = companionResolvent g L z b) ∧
    ((1 : Module.End ℚ ℚ) * referencePolynomialCoefficients 4 = 1 ∧
    referencePolynomialCoefficients 4 * (1 : Module.End ℚ ℚ) = 1 ∧
    coordinatePolynomial referencePolynomialCoefficients 2 * referenceCoordinateInverse = 1 ∧
    referenceCoordinateInverse * coordinatePolynomial referencePolynomialCoefficients 2 = 1)

end Artform.Scores.GravityBridge.Native.SlowCompanion.Statement
