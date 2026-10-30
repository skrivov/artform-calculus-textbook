import ArtformScores.GravityBridge.Defs

/-! # Registered statements for the gravity calculus campaign -/

namespace Artform.Scores.GravityBridge.Statement

open Artform.Scores

/-- **GAC:relations** (typed relations extend score laws).
Functional graphs compose in time order and distinguish complete matrix laws. -/
@[ledger "GAC:relations"]
def typedRelations : Prop :=
  (∀ (X Y Z W : Type) (r : Evolution X Y) (s : Evolution Y Z) (t : Evolution Z W),
    compose (compose r s) t = compose r (compose s t)) ∧
  (∀ (X Y Z : Type) (f : X → Y) (g : Y → Z),
    compose (graph f) (graph g) = graph (g ∘ f)) ∧
  (∀ (S : Type) [CommRing S], Function.Injective (matrixGraph (S := S))) ∧
  (∀ (S : Type) [CommRing S] (u v : Score S),
    matrixGraph (realize (u ++ v) : Matrix (Fin 2) (Fin 2) S) =
      compose (matrixGraph (realize u : Matrix (Fin 2) (Fin 2) S))
        (matrixGraph (realize v : Matrix (Fin 2) (Fin 2) S)))

/-- **GAC:realization** (invariance and all-time realization).
Image invariance is equivalent to exact intertwining. It implies, without
an observability assumption, agreement of every visible iterate. -/
@[ledger "GAC:realization"]
def invariantRealization : Prop :=
  ∀ (Y H : Type) (r : Realization Y H) (T : H → H),
    (r.Invariant T ↔ r.Intertwines T) ∧
    (r.Intertwines T → ∀ (n : ℕ) (y : Y),
      T^[n] (r.embed y) = r.embed ((r.visible T)^[n] y) ∧
      r.read (T^[n] (r.embed y)) = (r.visible T)^[n] y)

end Artform.Scores.GravityBridge.Statement
