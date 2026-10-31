import ArtformScores.GravityBridge.Native.Retrospective.ResidualReturnDefs
/-! # The exact independent connection return retains its residual -/
namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement
/-- **GAC2:connection-residual-return**
(the exact independent connection return retains its residual). -/
@[ledger "GAC2:connection-residual-return"]
def residualReturnLaw : Prop :=
  ∀ (K V W : Type) [Ring K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    (∀ (C : V →ₗ[K] W) (D E : W →ₗ[K] W)
    (_hED : ∀ a, E (D a) = a) (f u : V) (a v : W)
    (_h : C f + D a = 0),
    a - v = connectionGraph C E (f - u) - E (connectionResidual C D u v)) ∧
    (∀ (C : V →ₗ[K] W) (D E : W →ₗ[K] W)
    (_hDE : ∀ w, D (E w) = w) (f u : V) (a v : W)
    (_h : a - v = connectionGraph C E (f - u) - E (connectionResidual C D u v)),
    C f + D a = 0) ∧
    (∀ (C : V →ₗ[K] W) (D E : W →ₗ[K] W)
    (_hDE : ∀ w, D (E w) = w) (_hED : ∀ a, E (D a) = a) (f u : V) (a v : W),
    C f + D a = 0 ↔
    a - v = connectionGraph C E (f - u) - E (connectionResidual C D u v))
end Artform.Scores.GravityBridge.Native.Retrospective.Statement
