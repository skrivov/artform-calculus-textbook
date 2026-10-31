import ArtformScores.GravityBridge.LinearDefs

/-! # Separate quotient tests for evolution, sources and forms -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:quotient-compatibility** (compatible evolution, sources and forms). -/
@[ledger "GAC:quotient-compatibility"]
def quotientCompatibility : Prop :=
  ∀ (K X W : Type*) [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup W] [Module K W] (N : Submodule K X),
  (∀ T : X →ₗ[K] X,
    (∃ Tq : X ⧸ N →ₗ[K] X ⧸ N, Tq.comp N.mkQ = N.mkQ.comp T) ↔ N ≤ N.comap T) ∧
  (∀ O : X →ₗ[K] W,
    (∃ Oq : X ⧸ N →ₗ[K] W, Oq.comp N.mkQ = O) ↔ N ≤ LinearMap.ker O) ∧
  (∀ (J : Type*) (S : J → X →ₗ[K] K),
    (∀ j, ∃ Sq : X ⧸ N →ₗ[K] K, Sq.comp N.mkQ = S j) ↔
      ∀ j, N ≤ LinearMap.ker (S j)) ∧
  (∀ ω : LinearMap.BilinForm K X,
    (∃ ωq : LinearMap.BilinForm K (X ⧸ N),
      ∀ x y, ωq (N.mkQ x) (N.mkQ y) = ω x y) ↔
      (∀ n ∈ N, ∀ x, ω n x = 0) ∧ (∀ n ∈ N, ∀ x, ω x n = 0)) ∧
  (∀ (T : X →ₗ[K] X), N ≤ N.comap T → ∀ b x y : X,
    N.mkQ x = N.mkQ y → N.mkQ (T x + b) = N.mkQ (T y + b))

end Artform.Scores.GravityBridge.Statement
