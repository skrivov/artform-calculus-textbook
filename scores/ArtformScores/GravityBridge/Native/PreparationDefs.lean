import ArtformScores.GravityBridge.Native.Defs

/-! # Preparation data for the native signed connection equation -/

namespace Artform.Scores.GravityBridge.Native

open Matrix

/-- The complete covector source of the displayed distinct connection block. -/
def connectionSource (z : ℚ) : Fin 3 → ℚ := ![0, -z, z]

/-- The actual stationary connection, rather than a zero auxiliary register. -/
def connectionPreparation (z : ℚ) : Fin 3 → ℚ :=
  ![0, -2 * z / 103, 2 * z / 103]

/-- Closure of the original signed block equation for a proposed preparation. -/
def connectionEquation (z : ℚ) (c : Fin 3 → ℚ) : Prop :=
  connectionBlock *ᵥ c + (2 * kappa) • connectionSource z = 0

/-- The connection-dependent part of the original quadratic density.
The omitted pure-Z term is independent of c and has zero c-variation. -/
def connectionAction (z : ℚ) (c : Fin 3 → ℚ) : ℚ :=
  dotProduct c (connectionBlock *ᵥ c) / 2 +
    2 * kappa * dotProduct c (connectionSource z)

/-- The complete displayed torsion/connection block also retains kappa Z.M.Z.
It can be dropped for a c-variation, but not for a variation of the input z. -/
def completeConnectionAction (z : ℚ) (c : Fin 3 → ℚ) : ℚ :=
  -2 * kappa * z ^ 2 + connectionAction z c

/-- Christoffel input from the displayed leading TT wave at zero velocity.
The full native-to-wave correspondence is not part of this definition. -/
def christoffelInput (i j : Fin 3) : ℚ :=
  -(rhoSquared momentum) * polarization i j / 4

end Artform.Scores.GravityBridge.Native
