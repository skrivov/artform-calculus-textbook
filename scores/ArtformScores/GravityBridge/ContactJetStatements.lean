import ArtformScores.GravityBridge.ContactJetDefs

/-! # Complete polynomial jets and native input Hessians -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:source-contact-jets** (polynomial processing and native input Hessian). -/
@[ledger "GAC:source-contact-jets"]
def sourceContactJets : Prop :=
  (∀ (X X' Y Y' : Type*) [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (eX : X ≃ X') (eY : Y ≃ Y') (μ : X → Polynomial ℚ) (ν : Y → Polynomial ℚ)
    (ψ : X → Polynomial ℚ) (a : BoundaryKernel X Y (Polynomial ℚ))
    (φ : Y → Polynomial ℚ) (n : ℕ) (z : ℚ),
    sourceJet n
      (closedAmplitude (transportFunction eX μ) (transportFunction eY ν)
        (transportFunction eX ψ) (transportKernel eX eY a) (transportFunction eY φ)) z =
      sourceJet n (closedAmplitude μ ν ψ a φ) z) ∧
  (∀ (p q : Polynomial ℚ) (z : ℚ),
    sourceJet 2 (p * q) z = sourceJet 2 p z * sourceJet 0 q z +
      2 * sourceJet 1 p z * sourceJet 1 q z + sourceJet 0 p z * sourceJet 2 q z) ∧
  (∀ z : ℚ,
    completeInputPolynomial.eval z =
      Native.completeConnectionAction z (Native.connectionPreparation z) ∧
    connectionInputPolynomial.eval z =
      Native.connectionAction z (Native.connectionPreparation z) ∧
    sourceJet 2 completeInputPolynomial z = -4 / 103 ∧
    sourceJet 2 connectionInputPolynomial z = 8 / 10403 ∧
    sourceJet 2 completeInputPolynomial z - sourceJet 2 connectionInputPolynomial z = -4 / 101)

end Artform.Scores.GravityBridge.Statement
