import ArtformScores.GravityBridge.BoundaryAdjoint

/-! # Finite owned-panel variation and source covectors -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {K : Type*} [CommRing K]

def panelAction (c : K) (u : ℕ → K) (N : ℕ) : K :=
  ∑ i ∈ Finset.range N, c * (u (i + 1) - u i) ^ 2

def panelFlux (c : K) (u : ℕ → K) (i : ℕ) : K := 2 * c * (u (i + 1) - u i)

end Artform.Scores.GravityBridge.Native.GreenComposition
