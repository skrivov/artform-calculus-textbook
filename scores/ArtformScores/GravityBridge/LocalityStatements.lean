import ArtformScores.GravityBridge.LocalityDefs

/-! # Inverse and orbit support, with the channel scope explicit -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:local-processing** (inverse and orbit support in the two-channel class). -/
@[ledger "GAC:local-processing"]
def localProcessing : Prop :=
  (∀ (K : Type*) [CommRing K] (d : ℕ)
    (P : Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) (r : ℕ),
    MatrixStencilRadius (P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) r →
      MatrixStencilRadius (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) r) ∧
  (∀ (K : Type*) [CommRing K] (d : ℕ)
    (P : Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ)))
    (T : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) (r t n : ℕ),
    MatrixStencilRadius (P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) r →
      MatrixStencilRadius T t →
      MatrixStencilRadius (((P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) * T *
        (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ)))) ^ n)
        (n * t + 2 * r)) ∧
  (∃ A Q : Matrix (Fin 3) (Fin 3) (AddMonoidAlgebra ℚ (Fin 1 → ℤ)),
    A * Q = 1 ∧ Q * A = 1 ∧ MatrixStencilRadius A 1 ∧ ¬ MatrixStencilRadius Q 1)

end Artform.Scores.GravityBridge.Statement
