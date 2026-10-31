import ArtformScores.GravityBridge.Native.Retrospective.SourceActionDefs
/-! # Source-dependent stationary action and auxiliary reconstruction -/
namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement
/-- **GAC2:source-dependent-action-reconstruction**
(source-dependent stationary action and auxiliary reconstruction). -/
@[ledger "GAC2:source-dependent-action-reconstruction"]
def sourceActionLaw : Prop :=
  ∀ (K V W : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    (∀ (D : W →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (_hD : ∀ a b, D a b = D b a) (_hDE : ∀ l, D (E l) = l) (l m : W →ₗ[K] K),
    l (E m) = m (E l)) ∧
    (∀ (B : V →ₗ[K] W →ₗ[K] K)
    (D : W →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (_hDE : ∀ l, D (E l) = l) (_hED : ∀ a, E (D a) = a) (v : W →ₗ[K] K) (f : V) (a : W),
    B f + D a = v ↔ a = returnedAuxiliary B E v f) ∧
    (∀ (A : V →ₗ[K] V →ₗ[K] K) (B : V →ₗ[K] W →ₗ[K] K)
    (D : W →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (_hD : ∀ a b, D a b = D b a) (_hDE : ∀ l, D (E l) = l)
    (u : V →ₗ[K] K) (v : W →ₗ[K] K) (f : V) (a : W),
    sourceAction A B D u v f a = sourceEffective A B E u v f +
      D (a - returnedAuxiliary B E v f) (a - returnedAuxiliary B E v f) / 2) ∧
    (∀ (A : V →ₗ[K] V →ₗ[K] K) (B : V →ₗ[K] W →ₗ[K] K)
    (D : W →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (_hD : ∀ a b, D a b = D b a) (_hDE : ∀ l, D (E l) = l)
    (u : V →ₗ[K] K) (v : W →ₗ[K] K) (f : V),
    sourceAction A B D u v f (returnedAuxiliary B E v f) = sourceEffective A B E u v f) ∧
    (∀ (A : V →ₗ[K] V →ₗ[K] K) (B : V →ₗ[K] W →ₗ[K] K)
    (D : W →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (_hD : ∀ a b, D a b = D b a) (_hDE : ∀ l, D (E l) = l)
    (u : V →ₗ[K] K) (v : W →ₗ[K] K) (f : V),
    sourceEffective A B E u v f = (A f f - B f (E (B f))) / 2 -
      (u f - B f (E v)) - v (E v) / 2)
end Artform.Scores.GravityBridge.Native.Retrospective.Statement
