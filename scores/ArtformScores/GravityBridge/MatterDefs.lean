import ArtformScores.GravityBridge.LinearDefs

/-! # A declared scalar addition on a constant diagonal coframe chart -/

namespace Artform.Scores.GravityBridge

noncomputable section

def flatScalarKinetic (d : Fin 4 → ℚ) : ℚ :=
  -(d 0) ^ 2 + (d 1) ^ 2 + (d 2) ^ 2 + (d 3) ^ 2

def boostScalarGradient (d : Fin 4 → ℚ) : Fin 4 → ℚ :=
  ![(5 * d 0 + 4 * d 1) / 3, (4 * d 0 + 5 * d 1) / 3, d 2, d 3]

def scalarFrame (N a : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.diagonal ![N, a, a, a]

def scalarInverseFrame (N a : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.diagonal ![N⁻¹, a⁻¹, a⁻¹, a⁻¹]

def frameScalarGradient (N a : ℚ) (d : Fin 4 → ℚ) : Fin 4 → ℚ :=
  ![d 0 / N, d 1 / a, d 2 / a, d 3 / a]

def clockScalarDensity (N a coupling phi source : ℚ) (d : Fin 4 → ℚ) : ℚ :=
  -coupling / 2 * (N * a ^ 3) *
    (-(d 0) ^ 2 / N ^ 2 + ((d 1) ^ 2 + (d 2) ^ 2 + (d 3) ^ 2) / a ^ 2) - source * phi

def scalarFirstVariation (N a coupling source v : ℚ) (d e : Fin 4 → ℚ) : ℚ :=
  -coupling * (N * a ^ 3) *
    (-d 0 * e 0 / N ^ 2 + (d 1 * e 1 + d 2 * e 2 + d 3 * e 3) / a ^ 2) - source * v

end

end Artform.Scores.GravityBridge
