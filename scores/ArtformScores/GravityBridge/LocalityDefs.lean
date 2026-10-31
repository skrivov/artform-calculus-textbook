import ArtformScores.GravityBridge.StencilDefs

/-! # Matrix stencil radius and an explicit three-channel test -/

namespace Artform.Scores.GravityBridge

variable {K : Type*} [CommRing K] {d : ℕ}

def MatrixStencilRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) (AddMonoidAlgebra K (Fin d → ℤ)))
    (r : ℕ) : Prop := ∀ i j, HasStencilRadius (A i j) r

def threeShear {S : Type*} [Ring S] (p : S) : Matrix (Fin 3) (Fin 3) S :=
  !![1, p, 0; 0, 1, p; 0, 0, 1]

def threeShearBack {S : Type*} [Ring S] (p : S) : Matrix (Fin 3) (Fin 3) S :=
  !![1, -p, p ^ 2; 0, 1, -p; 0, 0, 1]

end Artform.Scores.GravityBridge
