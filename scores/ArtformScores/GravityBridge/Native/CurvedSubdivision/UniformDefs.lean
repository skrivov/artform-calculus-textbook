import ArtformScores.GravityBridge.Native.CurvedSubdivision.Cell
import ArtformScores.GravityBridge.Native.CurvedSubdivision.UniformBase

/-! # Original uniform subdivision has an interior detail residual -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40



noncomputable def vertexVariation {N : ℕ} (k : Fin (N + 1)) (v : Fin (N + 3)) : ℝ :=
  if v = (outgoingSlot k).castSucc then 1 else 0

noncomputable def perturbedPhase {N : ℕ} (k : Fin (N + 1)) (u t : ℝ) (v : Fin (N + 3)) : ℝ :=
  (v.val : ℝ) * u + t * vertexVariation k v

noncomputable def literalNativeChain {N : ℕ} (b : ℝ) (phi : Fin (N + 3) → ℝ) : ℝ :=
  ∑ e : Fin (N + 2), fullOriginalCell (1 / (N + 2 : ℝ)) b
    (Real.cosh (phi e.castSucc)) (Real.sinh (phi e.castSucc))
    (Real.cosh (phi e.succ)) (Real.sinh (phi e.succ))

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
