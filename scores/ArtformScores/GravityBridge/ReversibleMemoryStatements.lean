import ArtformScores.GravityBridge.Defs

/-! # Invariant preparation and finite retained information -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:reversible-memory** (invariant preparation and finite information). -/
@[ledger "GAC:reversible-memory"]
def reversibleMemory : Prop :=
  (∀ (Y H : Type*) (r : Realization Y H) (T : H ≃ H), r.Invariant T →
    Function.Injective (r.visible T) ∧
      (r.Invariant T.symm ↔ Function.Surjective (r.visible T))) ∧
  (∀ (Y H : Type*) [Finite Y] (r : Realization Y H) (T : H ≃ H), r.Invariant T →
    Function.Bijective (r.visible T)) ∧
  (∀ (X W M : Type*) [Finite M] (O : X → W) (m : X → M),
    Function.Injective (fun x => (O x, m x)) → ∀ w : W,
      Function.Injective (fun x : {x // O x = w} => m x.val) ∧
        Nat.card {x // O x = w} ≤ Nat.card M) ∧
  (∀ (Y Z : Type*) [Nonempty Y] (z0 : Z),
    Function.Injective (fun p : Y × Z => (p.1, z0)) ↔ Subsingleton Z)

end Artform.Scores.GravityBridge.Statement
