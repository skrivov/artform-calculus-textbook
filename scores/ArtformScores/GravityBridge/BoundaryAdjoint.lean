import ArtformScores.GravityBridge.BoundaryAdjointStatements

/-! # Finite Green identity and the open native-move boundary obligation -/

namespace Artform.Scores.GravityBridge

noncomputable section

open Finset

lemma finite_green_identity (f g : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ range n, forwardDifference f i * g i) +
      (∑ i ∈ range n, f (i + 1) * forwardDifference g i) = edgeBoundaryPair f g n := by
  induction n with
  | zero => simp [edgeBoundaryPair]
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    unfold forwardDifference edgeBoundaryPair at *
    linear_combination ih

lemma finite_green_without_boundary_iff (f g : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ range n, forwardDifference f i * g i) =
      -(∑ i ∈ range n, f (i + 1) * forwardDifference g i) ↔ f n * g n = f 0 * g 0 := by
  have h := finite_green_identity f g n
  unfold edgeBoundaryPair at h
  constructor <;> intro he <;> linarith

/-- One all-spatial torsion component of the pinned flat quadratic candidate. -/
lemma native_edge_variation (u0 u1 v0 v1 e : ℚ) :
    nativeEdgeTorsion (u0 + e * v0) (u1 + e * v1) =
      nativeEdgeTorsion u0 u1 + e * (2 * Native.kappa * (u1 - u0) * (v1 - v0)) +
        e ^ 2 * Native.kappa * (v1 - v0) ^ 2 := by
  dsimp [nativeEdgeTorsion]
  ring

lemma native_edge_boundary (u0 u1 v0 v1 : ℚ) :
    2 * Native.kappa * (u1 - u0) * (v1 - v0) =
      (2 * Native.kappa * (u1 - u0)) * v1 -
        (2 * Native.kappa * (u1 - u0)) * v0 := by ring

/-- **GAC:finite-boundary-adjoint** (the actual endpoint term in finite shift transposition). -/
@[ledger "GAC:finite-boundary-adjoint"]
theorem boundaryAdjointLaw : Statement.boundaryAdjointLaw := by
  exact ⟨finite_green_identity, finite_green_without_boundary_iff,
    native_edge_variation, native_edge_boundary⟩

/-! ## Non-vacuity -/

example :
    (∑ i ∈ range 1, forwardDifference (fun n : ℕ => (n : ℚ)) i * (1 : ℚ)) = 1 ∧
    (∑ i ∈ range 1, (i + 1 : ℚ) * forwardDifference (fun _ : ℕ => (1 : ℚ)) i) = 0 ∧
    edgeBoundaryPair (fun n : ℕ => (n : ℚ)) (fun _ => 1) 1 = 1 := by
  norm_num [forwardDifference, edgeBoundaryPair]

example : nativeEdgeTorsion 0 1 = 1 / 101 ∧
    2 * Native.kappa * (1 - 0) * (1 - 0) = 2 / 101 := by
  norm_num [nativeEdgeTorsion, Native.kappa]

end

end Artform.Scores.GravityBridge
