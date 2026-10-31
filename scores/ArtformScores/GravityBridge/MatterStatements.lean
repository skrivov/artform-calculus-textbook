import ArtformScores.GravityBridge.MatterDefs

/-! # Scalar coframe chart geometry and source variation -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:scalar-coframe-candidate** (scalar coframe chart geometry and source variation). -/
@[ledger "GAC:scalar-coframe-candidate"]
def matterLaw : Prop :=
  (∀ N a : ℚ, (scalarFrame N a).det = N * a ^ 3) ∧
  (∀ N a : ℚ, N ≠ 0 → a ≠ 0 →
    scalarFrame N a * scalarInverseFrame N a = 1 ∧
    scalarInverseFrame N a * scalarFrame N a = 1) ∧
  (∀ (N a coupling phi source : ℚ) (d : Fin 4 → ℚ),
    clockScalarDensity N a coupling phi source d =
      -coupling / 2 * (scalarFrame N a).det *
        flatScalarKinetic (frameScalarGradient N a d) - source * phi) ∧
  (∀ (N a coupling phi source : ℚ) (d : Fin 4 → ℚ), N ≠ 0 → a ≠ 0 →
    clockScalarDensity N a coupling phi source d =
      coupling * a ^ 3 / (2 * N) * (d 0) ^ 2 -
      coupling * N * a / 2 * ((d 1) ^ 2 + (d 2) ^ 2 + (d 3) ^ 2) - source * phi) ∧
  (∀ d : Fin 4 → ℚ, flatScalarKinetic (boostScalarGradient d) = flatScalarKinetic d) ∧
  (∀ (coupling phi source : ℚ) (d : Fin 4 → ℚ),
    clockScalarDensity 1 1 coupling phi source (boostScalarGradient d) =
      clockScalarDensity 1 1 coupling phi source d) ∧
  (∀ (N a coupling phi source v eps : ℚ) (d e : Fin 4 → ℚ),
    clockScalarDensity N a coupling (phi + eps * v) source (d + eps • e) =
      clockScalarDensity N a coupling phi source d +
      eps * scalarFirstVariation N a coupling source v d e +
      eps ^ 2 * clockScalarDensity N a coupling 0 0 e)

end Artform.Scores.GravityBridge.Statement
