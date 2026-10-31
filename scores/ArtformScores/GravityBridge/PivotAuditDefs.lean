import ArtformScores.GravityBridge.Native.R2ZeroRow
/-! # Native guarded pivot substitution -/
namespace Artform.Scores.GravityBridge
noncomputable section
open Native.R2
def pivotLatitude (l n : Fin 4 → ℝ) (i : Fin 4) : ℝ := -n i / l i
def pivotNormal (l n : Fin 4 → ℝ) (nu k : ℝ) (i : Fin 4) : ℝ :=
  (n i) ^ 2 - nu * n i * l i + k * (l i) ^ 2
end
end Artform.Scores.GravityBridge
