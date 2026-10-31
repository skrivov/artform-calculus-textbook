import ArtformScores.GravityBridge.Native.NativeCurrent.RadicalDefs

/-! # Admitted source-restricted current radical -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent.Statement

/-- **GAC2:admitted-source-current-radical**
(admitted source-restricted current radical). -/
@[ledger "GAC2:admitted-source-current-radical"]
def radicalLaw : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V],
    (∀ (W : Submodule K V) (B : V →ₗ[K] V →ₗ[K] K) (g : V),
    g ∈ admittedRadical W B ↔ g ∈ W ∧ ∀ w ∈ W, B g w = 0) ∧
    (∀ (W : Submodule K V)
    (B : V →ₗ[K] V →ₗ[K] K) (A : Module.End K V)
    (_hW : ∀ w ∈ W, A w ∈ W)
    (_hconserve : ∀ g ∈ W, ∀ w ∈ W, B (A g) w + B g (A w) = 0),
    ∀ g ∈ admittedRadical W B, A g ∈ admittedRadical W B) ∧
    (∀ (W : Submodule K V)
    (B : V →ₗ[K] V →ₗ[K] K)
    (_hnondeg : ∀ g ∈ W, (∀ w ∈ W, B g w = 0) → g = 0),
    admittedRadical W B = ⊥) ∧
    (∀ (W : Submodule K V) (B : V →ₗ[K] V →ₗ[K] K)
    (J : Module.End K V) (g : V),
    g ∈ admittedRadical (W⊓J.ker) B ↔
      g ∈ W ∧ J g = 0 ∧ ∀ w, w ∈ W → J w = 0 → B g w = 0)

end Artform.Scores.GravityBridge.Native.NativeCurrent.Statement
