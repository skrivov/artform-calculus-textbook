import ArtformScores.GravityBridge.ChangingGeometryStatements

/-! # Incidence-compatible changing geometry and retained edge detail -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma subdivision_chain : edgeAggregation.comp fineGradient =
    coarseGradient.comp vertexRestriction := by
  apply LinearMap.ext
  intro u
  dsimp [edgeAggregation, fineGradient, coarseGradient, vertexRestriction]
  ring

lemma subdivision_retraction : vertexRestriction.comp midpointRefinement = LinearMap.id := by
  apply LinearMap.ext
  intro u
  ext i
  fin_cases i <;> simp [vertexRestriction, midpointRefinement]

lemma refined_gradient (u : Fin 2 → ℚ) :
    fineGradient (midpointRefinement u) = ![coarseGradient u / 2, coarseGradient u / 2] := by
  ext i
  fin_cases i <;> simp [fineGradient, midpointRefinement, coarseGradient] <;> ring

lemma aggregate_fiber (e f : Fin 2 → ℚ) :
    edgeAggregation e = edgeAggregation f ↔ ∃ d : ℚ, f = e + ![d, -d] := by
  constructor
  · intro h
    refine ⟨f 0 - e 0, ?_⟩
    have hs : e 0 + e 1 = f 0 + f 1 := h
    ext i
    fin_cases i <;> simp
    all_goals linarith
  · rintro ⟨d, rfl⟩
    simp [edgeAggregation, Matrix.vecHead, Matrix.vecTail]
    ring

/-- **GAC:changing-geometry** (a checked nontrivial subdivision and its detail). -/
@[ledger "GAC:changing-geometry"]
theorem changingGeometry : Statement.changingGeometry := by
  exact ⟨subdivision_chain, subdivision_retraction, refined_gradient, aggregate_fiber,
    edgeDetailEquiv.symm_apply_apply, edgeDetailEquiv.apply_symm_apply⟩

/-! ## Non-vacuity -/

example : fineGradient ![1, 3, 6] = ![2, 3] ∧
    edgeAggregation (fineGradient ![1, 3, 6]) = coarseGradient ![1, 6] := by
  norm_num [fineGradient, edgeAggregation, coarseGradient]

example : edgeAggregation (![1, 0] : Fin 2 → ℚ) = edgeAggregation ![0, 1] ∧
    (![1, 0] : Fin 2 → ℚ) ≠ ![0, 1] := by
  constructor
  · norm_num [edgeAggregation]
  · intro h
    have := congrFun h 0
    norm_num at this

example : edgeDetailEquiv (![2, 3] : Fin 2 → ℚ) = (5, -1) ∧
    edgeDetailEquiv.symm (5, -1) = ![2, 3] := by norm_num [edgeDetailEquiv]

end

end Artform.Scores.GravityBridge
