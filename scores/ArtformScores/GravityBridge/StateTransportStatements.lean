import ArtformScores.GravityBridge.StateTransportDefs

/-! # Algebraic state pullback and finite CCR scope -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:algebraic-state-transport** (algebraic state pullback and finite ccr scope). -/
@[ledger "GAC:algebraic-state-transport"]
def stateTransportLaw : Prop :=
  (∀ (A B : Type*) [Semiring A] [StarRing A] [Algebra ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] (s : AlgebraicPositiveState A)
    (f : B →⋆ₐ[ℂ] A),
      (s.pullback f).functional 1 = 1 ∧
      ∀ b, ((s.pullback f).functional (star b * b)).im = 0 ∧
        0 ≤ ((s.pullback f).functional (star b * b)).re) ∧
  (∀ (A B : Type*) [Semiring A] [StarRing A] [Algebra ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] (s : AlgebraicPositiveState A)
    (f : B →⋆ₐ[ℂ] A) (alpha : A →⋆ₐ[ℂ] A) (beta : B →⋆ₐ[ℂ] B),
    (∀ a, s.functional (alpha a) = s.functional a) →
    (∀ b, f (beta b) = alpha (f b)) →
    ∀ b, (s.pullback f).functional (beta b) = (s.pullback f).functional b) ∧
  ((zeroVectorState.pullback binarySwapAut).functional binaryZ = -1) ∧
  (∀ n : ℕ, 0 < n → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    A * B - B * A ≠ Complex.I • 1)

end Artform.Scores.GravityBridge.Statement
