import ArtformScores.GravityBridge.ChangingGeometryDefs

/-! # Incidence-compatible subdivision and exact detail recovery -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:changing-geometry** (edge subdivision commutes with incidence and retains detail). -/
@[ledger "GAC:changing-geometry"]
def changingGeometry : Prop :=
  edgeAggregation.comp fineGradient = coarseGradient.comp vertexRestriction ∧
  vertexRestriction.comp midpointRefinement = LinearMap.id ∧
  (∀ u : Fin 2 → ℚ, fineGradient (midpointRefinement u) =
    ![coarseGradient u / 2, coarseGradient u / 2]) ∧
  (∀ e f : Fin 2 → ℚ,
    edgeAggregation e = edgeAggregation f ↔ ∃ d : ℚ, f = e + ![d, -d]) ∧
  (∀ e : Fin 2 → ℚ, edgeDetailEquiv.symm (edgeDetailEquiv e) = e) ∧
  (∀ p : ℚ × ℚ, edgeDetailEquiv (edgeDetailEquiv.symm p) = p)

end Artform.Scores.GravityBridge.Statement
