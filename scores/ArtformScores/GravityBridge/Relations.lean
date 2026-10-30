import ArtformScores.GravityBridge.Statements

/-! # Typed relations preserve the existing score semantics -/

namespace Artform.Scores.GravityBridge

theorem compose_assoc {X Y Z W : Type*} (r : Evolution X Y) (s : Evolution Y Z)
    (t : Evolution Z W) : compose (compose r s) t = compose r (compose s t) := by
  funext x w
  apply propext
  constructor
  · rintro ⟨z, ⟨y, hr, hs⟩, ht⟩
    exact ⟨y, hr, z, hs, ht⟩
  · rintro ⟨y, hr, z, hs, ht⟩
    exact ⟨z, ⟨y, hr, hs⟩, ht⟩

theorem compose_graph {X Y Z : Type*} (f : X → Y) (g : Y → Z) :
    compose (graph f) (graph g) = graph (g ∘ f) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, rfl, h⟩
    exact h
  · intro h
    exact ⟨f x, rfl, h⟩

theorem graph_injective {X Y : Type*} : Function.Injective (graph (X := X) (Y := Y)) := by
  intro f g h
  funext x
  have hf : graph f x (f x) := rfl
  rw [h] at hf
  exact hf.symm

theorem compose_graph_id_left {X Y : Type*} (r : Evolution X Y) :
    compose (graph id) r = r := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, rfl, h⟩
    exact h
  · exact fun h => ⟨x, rfl, h⟩

theorem compose_graph_id_right {X Y : Type*} (r : Evolution X Y) :
    compose r (graph id) = r := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, h, rfl⟩
    exact h
  · exact fun h => ⟨y, h, rfl⟩

theorem matrixGraph_injective {S : Type*} [CommRing S] :
    Function.Injective (matrixGraph (S := S)) := by
  intro A B h
  exact Matrix.mulVec_injective (graph_injective h)

theorem scoreGraph_append {S : Type*} [CommRing S] (u v : Score S) :
    matrixGraph (realize (u ++ v) : Matrix (Fin 2) (Fin 2) S) =
      compose (matrixGraph (realize u : Matrix (Fin 2) (Fin 2) S))
        (matrixGraph (realize v : Matrix (Fin 2) (Fin 2) S)) := by
  rw [realize_append, Matrix.SpecialLinearGroup.coe_mul, matrixGraph,
    matrixGraph, matrixGraph, compose_graph]
  congr 1
  funext x
  exact (Matrix.mulVec_mulVec x _ _).symm

/-- **GAC:relations** (typed relations extend score laws). -/
@[ledger "GAC:relations"]
theorem typedRelations : Statement.typedRelations := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y Z W r s t
    exact compose_assoc r s t
  · intro X Y Z f g
    exact compose_graph f g
  · intro S inst
    exact matrixGraph_injective
  · intro S inst u v
    exact scoreGraph_append u v

/-! ## Non-vacuity -/

/-- The book's kick and move compose with the same time order in the extension. -/
example :
    matrixGraph (realize [Step.kick (1 : ℚ), Step.move (-2)] :
      Matrix (Fin 2) (Fin 2) ℚ) =
    compose (matrixGraph (Step.kick (1 : ℚ)).mat)
      (matrixGraph (Step.move (-2 : ℚ)).mat) := by
  simpa [realize_singleton] using
    scoreGraph_append [Step.kick (1 : ℚ)] [Step.move (-2)]

/-- The larger relation language includes genuine nonuniqueness. -/
example : ∃ r : Evolution ℚ ℚ, r 0 0 ∧ r 0 1 :=
  ⟨fun _ _ => True, trivial, trivial⟩

end Artform.Scores.GravityBridge
