import ArtformScores.GravityBridge.Native.NativeCurrent.OwnedWindow

/-! # Finite-range temporal cut with its original incoming terms -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {K : Type*} [CommRing K]

def cutSum (edge : ℤ → ℕ → K) (R : ℕ) (n : ℤ) : K :=
  ∑ r ∈ Finset.range (R + 1), ∑ j ∈ Finset.range r, edge (n - (j : ℤ)) r

def rowSkew (edge : ℤ → ℕ → K) (R : ℕ) (n : ℤ) : K :=
  ∑ r ∈ Finset.range (R + 1), (edge n r - edge (n - (r : ℤ)) r)

def operatorEdge {V : Type*} (B : ℕ → V → V → K) (x y : ℤ → V) (n : ℤ) (r : ℕ) : K :=
  B r (x n) (y (n + (r : ℤ))) - B r (y n) (x (n + (r : ℤ)))

def pairedIncomingStencil {V : Type*} (B : ℕ → V → V → K) (x y : ℤ → V)
    (R : ℕ) (n : ℤ) : K :=
  ∑ r ∈ Finset.range (R + 1), (B r (x n) (y (n + (r : ℤ))) +
    B r (y (n - (r : ℤ))) (x n))

end Artform.Scores.GravityBridge.Native.GreenComposition
