import ArtformScores.GravityBridge.BoundaryAdjointDefs

/-! # Finite adjoints retain endpoint terms -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:finite-boundary-adjoint** (finite adjoints retain endpoint terms). -/
@[ledger "GAC:finite-boundary-adjoint"]
def boundaryAdjointLaw : Prop :=
  (∀ (f g : ℕ → ℚ) (n : ℕ),
    (∑ i ∈ Finset.range n, forwardDifference f i * g i) +
      (∑ i ∈ Finset.range n, f (i + 1) * forwardDifference g i) = edgeBoundaryPair f g n) ∧
  (∀ (f g : ℕ → ℚ) (n : ℕ),
    (∑ i ∈ Finset.range n, forwardDifference f i * g i) =
      -(∑ i ∈ Finset.range n, f (i + 1) * forwardDifference g i) ↔ f n * g n = f 0 * g 0) ∧
  (∀ u0 u1 v0 v1 e : ℚ,
    nativeEdgeTorsion (u0 + e * v0) (u1 + e * v1) =
      nativeEdgeTorsion u0 u1 + e * (2 * Native.kappa * (u1 - u0) * (v1 - v0)) +
        e ^ 2 * Native.kappa * (v1 - v0) ^ 2) ∧
  (∀ u0 u1 v0 v1 : ℚ,
    2 * Native.kappa * (u1 - u0) * (v1 - v0) =
      (2 * Native.kappa * (u1 - u0)) * v1 -
        (2 * Native.kappa * (u1 - u0)) * v0)

end Artform.Scores.GravityBridge.Statement
