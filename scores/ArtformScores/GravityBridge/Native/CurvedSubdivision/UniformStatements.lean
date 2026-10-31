import ArtformScores.GravityBridge.Native.CurvedSubdivision.UniformDefs

/-! # Original uniform subdivision has an interior detail residual -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement

open Matrix Full40

/-- **GAC2:native-uniform-detail-residual**
(original uniform subdivision has an interior detail residual). -/
@[ledger "GAC2:native-uniform-detail-residual"]
noncomputable def uniformLaw : Prop :=
    (∀ {N : ℕ} (k : Fin (N + 1)) (e : Fin (N + 2)),
    vertexVariation k e.castSucc = rootVariation k e ∧
    vertexVariation k e.succ - rootVariation k e = edgeVariation k e) ∧
    (∀ {N : ℕ} (k : Fin (N + 1)) (u t : ℝ),
    perturbedPhase k u t 0 = 0 ∧
      perturbedPhase k u t (Fin.last (N + 2)) = (N + 2 : ℝ) * u) ∧
    (∀ {N : ℕ} (k : Fin (N + 1)) (e : Fin (N + 2)) (u t : ℝ),
    perturbedPhase k u t e.succ - perturbedPhase k u t e.castSucc =
      u + t * edgeVariation k e) ∧
    (∀ {N : ℕ} (k : Fin (N + 1)) (b u t : ℝ) (_hb : b ≠ 0),
    literalNativeChain b (perturbedPhase k u t) = uniformNativeDetail k b u t) ∧
    (∀ {N : ℕ} (k : Fin (N + 1)) (b u : ℝ)
    (_hb : 0 < b) (_hu : 0 < u),
    HasDerivAt (fun t => literalNativeChain b (perturbedPhase k u t))
      (-(2 / 101 : ℝ) * (b / (N + 2)) * Real.sinh (((k.val + 1 : ℕ) : ℝ) * u)) 0 ∧
    -(2 / 101 : ℝ) * (b / (N + 2)) * Real.sinh (((k.val + 1 : ℕ) : ℝ) * u) ≠ 0)

end Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement
