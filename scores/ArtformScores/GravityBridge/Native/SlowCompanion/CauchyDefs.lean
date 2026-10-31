import ArtformScores.GravityBridge.Native.R7Blocks.Sylvester

/-! # Original mixed Cauchy polynomial and lower-basis contact -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion

variable {K V T : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup T] [Module K T]

def coordinatePolynomial (g : Fin 5 → Module.End K V) (z : K) : Module.End K V :=
  g 0 + z • g 1 + z ^ 2 • g 2 + z ^ 3 • g 3 + z ^ 4 • g 4

def coordinateCauchy (g : Fin 5 → Module.End K V) (z : K) (x : Fin 4 → V) : V :=
  g 1 (x 0) + g 2 (z • x 0 + x 1) + g 3 (z ^ 2 • x 0 + z • x 1 + x 2) +
    g 4 (z ^ 3 • x 0 + z ^ 2 • x 1 + z • x 2 + x 3)

def mixedCauchy (g : Fin 5 → Module.End K V) (C1 : T →ₗ[K] V)
    (z : K) (t₀ t₁ : T) (x : Fin 4 → V) : T × V :=
  (z • t₀ + t₁, coordinateCauchy g z x + C1 t₀)

def lowerCoefficients (J : Module.End K V) (g : Fin 5 → Module.End K V) :
    Fin 5 → Module.End K V := fun j => J * g j * J

def lowerJets (J : Module.End K V) (x : Fin 4 → V) : Fin 4 → V := fun j => J (x j)

end Artform.Scores.GravityBridge.Native.SlowCompanion
