import ArtformScores.Basic

/-!
# Typed evolution and visible realizations

Definitions for the gravity campaign's algebraic foundation. A relation may
be partial or multivalued. Its functional special case retains the existing
score realizer's time order.
-/

namespace Artform.Scores.GravityBridge

/-- A typed evolution relation, without existence or uniqueness assumptions. -/
abbrev Evolution (X Y : Type*) := X → Y → Prop

/-- First evolve by r, then by s. -/
def compose {X Y Z : Type*} (r : Evolution X Y) (s : Evolution Y Z) :
    Evolution X Z := fun x z => ∃ y, r x y ∧ s y z

/-- The relation of a function. -/
def graph {X Y : Type*} (f : X → Y) : Evolution X Y := fun x y => f x = y

/-- The relation of a two-channel matrix law. -/
def matrixGraph {S : Type*} [CommRing S] (A : Matrix (Fin 2) (Fin 2) S) :
    Evolution (Fin 2 → S) (Fin 2 → S) := graph A.mulVec

/-- An embedding/readout pair, including a proof that all visible data are recovered. -/
structure Realization (Y H : Type*) where
  embed : Y → H
  read : H → Y
  recover : Function.LeftInverse read embed

/-- The visible one-step law obtained by embedding, evolving and reading. -/
def Realization.visible {Y H : Type*} (r : Realization Y H) (T : H → H) : Y → Y :=
  r.read ∘ T ∘ r.embed

/-- Forward preservation of the actual embedded image. -/
def Realization.Invariant {Y H : Type*} (r : Realization Y H) (T : H → H) : Prop :=
  ∀ y, T (r.embed y) ∈ Set.range r.embed

/-- Exact realization of the visible evolution, before discarding any variables. -/
def Realization.Intertwines {Y H : Type*} (r : Realization Y H) (T : H → H) : Prop :=
  ∀ y, T (r.embed y) = r.embed (r.visible T y)

end Artform.Scores.GravityBridge
