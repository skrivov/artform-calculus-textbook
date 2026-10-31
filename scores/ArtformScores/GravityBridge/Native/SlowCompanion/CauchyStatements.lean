import ArtformScores.GravityBridge.Native.SlowCompanion.CauchyDefs

/-! # Original mixed Cauchy polynomial and lower-basis contact -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion.Statement

/-- **GAC2:native-cauchy-polynomial-lower-basis**
(original mixed cauchy polynomial and lower-basis contact). -/
@[ledger "GAC2:native-cauchy-polynomial-lower-basis"]
def cauchyLaw : Prop :=
  ∀ (K V T : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup T] [Module K T],
    (∀ (g : Fin 5 → Module.End K V) (z : K) (x : Fin 4 → V),
    coordinateCauchy g z x =
      g 1 (x 0) + z • g 2 (x 0) + g 2 (x 1) + z ^ 2 • g 3 (x 0) +
      z • g 3 (x 1) + g 3 (x 2) + z ^ 3 • g 4 (x 0) + z ^ 2 • g 4 (x 1) +
      z • g 4 (x 2) + g 4 (x 3)) ∧
    (∀ (J : Module.End K V) (g : Fin 5 → Module.End K V)
    (z : K) (x : Fin 4 → V) (_hJ : J * J = 1),
    coordinateCauchy (lowerCoefficients J g) z (lowerJets J x) =
      J (coordinateCauchy g z x)) ∧
    (∀ (J : Module.End K V) (g : Fin 5 → Module.End K V)
    (z : K),
    coordinatePolynomial (lowerCoefficients J g) z =
      J * (coordinatePolynomial g z) * J) ∧
    (∀ (J : Module.End K V) (g : Fin 5 → Module.End K V)
    (C1 : T →ₗ[K] V) (z : K) (t₀ t₁ : T) (x : Fin 4 → V) (_hJ : J * J = 1),
    mixedCauchy (lowerCoefficients J g) (J.comp C1) z t₀ t₁ (lowerJets J x) =
      (z • t₀ + t₁, J ((mixedCauchy g C1 z t₀ t₁ x).2))) ∧
    (∀ (g : Fin 5 → Module.End K V)
    (C1 : T →ₗ[K] V) (z : K) (t₀ t₁ : T),
    mixedCauchy g C1 z t₀ t₁ 0 = (z • t₀ + t₁, C1 t₀))

end Artform.Scores.GravityBridge.Native.SlowCompanion.Statement
