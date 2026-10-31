import ArtformScores.GravityBridge.Native.Retrospective.ResidualReturnStatements
/-! # The exact independent connection return retains its residual -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
variable {K V W : Type*} [Ring K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
lemma exact_residual_return (C : V →ₗ[K] W) (D E : W →ₗ[K] W)
    (hED : ∀ a, E (D a) = a) (f u : V) (a v : W)
    (h : C f + D a = 0) :
    a - v = connectionGraph C E (f - u) - E (connectionResidual C D u v) := by
  have hd : D a = -C f := by
    calc
      D a = D a - (C f + D a) := by rw [h, sub_zero]
      _ = -C f := by abel
  have ha : a = -E (C f) := by rw [← hED a, hd, map_neg]
  simp only [connectionGraph, connectionResidual, LinearMap.neg_apply,
    LinearMap.comp_apply, map_sub, map_add, hED]
  rw [ha]
  abel
lemma residual_return_converse (C : V →ₗ[K] W) (D E : W →ₗ[K] W)
    (hDE : ∀ w, D (E w) = w) (f u : V) (a v : W)
    (h : a - v = connectionGraph C E (f - u) - E (connectionResidual C D u v)) :
    C f + D a = 0 := by
  have hd := congrArg D h
  simp only [connectionGraph, connectionResidual, LinearMap.neg_apply,
    LinearMap.comp_apply, map_sub, map_add, map_neg, hDE] at hd
  calc
    C f + D a = C f + ((D a - D v) + D v) := by abel
    _ = C f + ((-(C f - C u) - (C u + D v)) + D v) := by rw [hd]; abel
    _ = 0 := by abel
lemma residual_return_iff (C : V →ₗ[K] W) (D E : W →ₗ[K] W)
    (hDE : ∀ w, D (E w) = w) (hED : ∀ a, E (D a) = a) (f u : V) (a v : W) :
    C f + D a = 0 ↔
    a - v = connectionGraph C E (f - u) - E (connectionResidual C D u v) :=
  ⟨exact_residual_return C D E hED f u a v, residual_return_converse C D E hDE f u a v⟩
/-- **GAC2:connection-residual-return**
(the exact independent connection return retains its residual). -/
@[ledger "GAC2:connection-residual-return"]
theorem residualReturnLaw : Statement.residualReturnLaw := by
  intro K V W _ _ _ _ _
  exact ⟨exact_residual_return,
    residual_return_converse,
    residual_return_iff⟩
/-! ## Non-vacuity -/
example : (∀ w : ℚ, schurToyScale 1 (schurToyScale 1 w) = w) ∧
    connectionResidual (schurToyScale 1) (schurToyScale 1) (0 : ℚ) 1 = 1 ∧
    connectionGraph (schurToyScale 1) (schurToyScale 1) (0 - 0 : ℚ) -
      schurToyScale 1 (connectionResidual (schurToyScale 1) (schurToyScale 1) 0 1) = -1 ∧
    (0 - 1 : ℚ) ≠ connectionGraph (schurToyScale 1) (schurToyScale 1) (0 - 0) := by
  constructor
  · intro w
    norm_num [schurToyScale]
  · norm_num [connectionResidual, connectionGraph, schurToyScale]
end Artform.Scores.GravityBridge.Native.Retrospective
