import ArtformScores.GravityBridge.Native.SlowCompanion.Cauchy

/-! # Guarded resolvent of the complete four-jet companion -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def coordinateStep (g : Fin 5 → Module.End K V) (H : Module.End K V)
    (x : Fin 4 → V) : Fin 4 → V :=
  ![x 1, x 2, x 3, -H (g 0 (x 0) + g 1 (x 1) + g 2 (x 2) + g 3 (x 3))]

def resolventState (z : K) (v : V) (b : Fin 4 → V) : Fin 4 → V :=
  ![v, z • v - b 0, z ^ 2 • v - z • b 0 - b 1, z ^ 3 • v - z ^ 2 • b 0 - z • b 1 - b 2]

def companionResolvent (g : Fin 5 → Module.End K V) (L : Module.End K V)
    (z : K) (b : Fin 4 → V) : Fin 4 → V :=
  resolventState z (L (coordinateCauchy g z b)) b

def referencePolynomialCoefficients : Fin 5 → Module.End ℚ ℚ :=
  fun j => if j = 4 then 1 else 0

def referenceCoordinateInverse : Module.End ℚ ℚ := (1 / 16 : ℚ) • 1

end Artform.Scores.GravityBridge.Native.SlowCompanion
