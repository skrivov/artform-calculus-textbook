import ArtformScores.GravityBridge.Defs

/-!
# The native signed distinct block and a rational TT witness

These are the literal finite blocks in the scoped M162 source. The source's
full forty-equation derivation and Fourier packet analysis are separate
application obligations; defining this block does not assume them as axioms.
-/

namespace Artform.Scores.GravityBridge.Native

open Matrix

/-- Original torsion coefficient. -/
def kappa : ℚ := 1 / 101

/-- The three connection coordinates in the distinct triple (0,i,j). -/
def torsionBlock : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-1, 1, 0; 1, 0, -1; 0, -1, -1]

/-- The original signed covector pairing, not a positive face metric. -/
def facePairing : Matrix (Fin 3) (Fin 3) ℚ := -1

/-- Hessian of the curvature quadratic -xy-xz+yz. -/
def curvatureBlock : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, -1, -1; -1, 0, 1; -1, 1, 0]

/-- The native connection Hessian including its signed torsion contribution. -/
def connectionBlock : Matrix (Fin 3) (Fin 3) ℚ :=
  curvatureBlock + (2 * kappa) • (torsionBlock.transpose * facePairing * torsionBlock)

/-- The initial Christoffel input in this triple. -/
def faceInput (z : ℚ) : Fin 3 → ℚ := ![z, z, 0]

/-- The complete signed Schur covector for this block. -/
noncomputable def schurCovector (z : ℚ) : Fin 3 → ℚ :=
  facePairing *ᵥ faceInput z -
    (2 * kappa) • ((facePairing * torsionBlock) *ᵥ
      (connectionBlock⁻¹ *ᵥ ((torsionBlock.transpose * facePairing) *ᵥ faceInput z)))

/-- The original three-dimensional witness momentum. -/
def momentum : Fin 3 → ℚ := ![1, 2, 3]

/-- Rational form of the source's normalized transverse traceless polarization. -/
def polarization : Matrix (Fin 3) (Fin 3) ℚ :=
  (1 / 70 : ℚ) • !![47, -46, 15; -46, -22, 30; 15, 30, -25]

/-- Squared Euclidean momentum. -/
def rhoSquared (k : Fin 3 → ℚ) : ℚ := ∑ j, k j * k j

/-- Diagonal momentum contraction; the Fourier derivative adds i. -/
def diagonalContraction (k : Fin 3 → ℚ) (q : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  ∑ j, k j * q j j

/-- The real coefficient of i in the lower temporal fourth-jet symbol.
Its identification with the full native response is an application bridge. -/
def temporalSymbol (k : Fin 3 → ℚ) (q : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  -(rhoSquared k) * diagonalContraction k q / 202

end Artform.Scores.GravityBridge.Native
