import ArtformScores.GravityBridge.Native.Retrospective.SourceActionStatements
/-! # Source-dependent stationary action and auxiliary reconstruction -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
variable {K V W : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
omit [CharZero K] [AddCommGroup V] [Module K V] in
lemma dual_inverse_symmetric (D : W →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (hD : ∀ a b, D a b = D b a) (hDE : ∀ l, D (E l) = l) (l m : W →ₗ[K] K) :
    l (E m) = m (E l) := by
  calc
    l (E m) = D (E l) (E m) := congrArg (fun z : W →ₗ[K] K => z (E m)) (hDE l).symm
    _ = D (E m) (E l) := hD _ _
    _ = m (E l) := congrArg (fun z : W →ₗ[K] K => z (E l)) (hDE m)
omit [CharZero K] in
lemma returned_auxiliary_equation (B : V →ₗ[K] W →ₗ[K] K)
    (D : W →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (hDE : ∀ l, D (E l) = l) (hED : ∀ a, E (D a) = a) (v : W →ₗ[K] K) (f : V) (a : W) :
    B f + D a = v ↔ a = returnedAuxiliary B E v f := by
  constructor
  · intro h
    have hd : D a = v - B f := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using h
    rw [returnedAuxiliary, ← hd, hED]
  · intro h
    rw [h, returnedAuxiliary, hDE]
    abel
lemma source_action_completion (A : V →ₗ[K] V →ₗ[K] K) (B : V →ₗ[K] W →ₗ[K] K)
    (D : W →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (hD : ∀ a b, D a b = D b a) (hDE : ∀ l, D (E l) = l)
    (u : V →ₗ[K] K) (v : W →ₗ[K] K) (f : V) (a : W) :
    sourceAction A B D u v f a = sourceEffective A B E u v f +
      D (a - returnedAuxiliary B E v f) (a - returnedAuxiliary B E v f) / 2 := by
  have hs := hD a (returnedAuxiliary B E v f)
  have ha : D (returnedAuxiliary B E v f) a = v a - B f a := by
    simp [returnedAuxiliary, hDE]
  have hb : D (returnedAuxiliary B E v f) (returnedAuxiliary B E v f) =
      v (returnedAuxiliary B E v f) - B f (returnedAuxiliary B E v f) := by
    simp [returnedAuxiliary, hDE]
  simp only [sourceAction, sourceEffective, map_sub, LinearMap.sub_apply]
  change _ = _ + (D a a - D (returnedAuxiliary B E v f) a -
    (D a (returnedAuxiliary B E v f) - D (returnedAuxiliary B E v f)
      (returnedAuxiliary B E v f))) / 2
  rw [hs, ha, hb]
  simp only [returnedAuxiliary, map_sub]
  ring
lemma source_action_on_return (A : V →ₗ[K] V →ₗ[K] K) (B : V →ₗ[K] W →ₗ[K] K)
    (D : W →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (hD : ∀ a b, D a b = D b a) (hDE : ∀ l, D (E l) = l)
    (u : V →ₗ[K] K) (v : W →ₗ[K] K) (f : V) :
    sourceAction A B D u v f (returnedAuxiliary B E v f) = sourceEffective A B E u v f := by
  rw [source_action_completion A B D E hD hDE]
  simp
lemma source_effective_expanded (A : V →ₗ[K] V →ₗ[K] K) (B : V →ₗ[K] W →ₗ[K] K)
    (D : W →ₗ[K] W →ₗ[K] K) (E : (W →ₗ[K] K) →ₗ[K] W)
    (hD : ∀ a b, D a b = D b a) (hDE : ∀ l, D (E l) = l)
    (u : V →ₗ[K] K) (v : W →ₗ[K] K) (f : V) :
    sourceEffective A B E u v f = (A f f - B f (E (B f))) / 2 -
      (u f - B f (E v)) - v (E v) / 2 := by
  have hs := dual_inverse_symmetric D E hD hDE v (B f)
  simp only [sourceEffective, map_sub, LinearMap.sub_apply]
  rw [hs]
  ring
/-- **GAC2:source-dependent-action-reconstruction**
(source-dependent stationary action and auxiliary reconstruction). -/
@[ledger "GAC2:source-dependent-action-reconstruction"]
theorem sourceActionLaw : Statement.sourceActionLaw := by
  intro K V W _ _ _ _ _ _
  exact ⟨dual_inverse_symmetric,
    returned_auxiliary_equation,
    source_action_completion,
    source_action_on_return,
    source_effective_expanded⟩
/-! ## Non-vacuity -/
def scalarForm (c : ℚ) : ℚ →ₗ[ℚ] ℚ →ₗ[ℚ] ℚ :=
  { toFun := fun x => (c * x) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
    map_add' := by intros; ext; simp; ring
    map_smul' := by intros; ext; simp; ring }
def scalarReturn : (ℚ →ₗ[ℚ] ℚ) →ₗ[ℚ] ℚ :=
  { toFun := fun l => l 1 / 2
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp; ring }
example : (∀ l, scalarForm 2 (scalarReturn l) = l) ∧
    (∀ a, scalarReturn (scalarForm 2 a) = a) ∧
    returnedAuxiliary (scalarForm 1) scalarReturn (schurToyScale 5) 1 = 2 ∧
    sourceAction (scalarForm 3) (scalarForm 1) (scalarForm 2)
      (schurToyScale 4) (schurToyScale 5) 1 2 = -13 / 2 ∧
    sourceEffective (scalarForm 3) (scalarForm 1) scalarReturn
      (schurToyScale 4) (schurToyScale 5) 1 = -13 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro l
    ext
    norm_num [scalarForm, scalarReturn]
    ring
  · intro a
    norm_num [scalarForm, scalarReturn]
    ring
  · norm_num [returnedAuxiliary, scalarForm, scalarReturn, schurToyScale]
  · norm_num [sourceAction, scalarForm, schurToyScale]
  · norm_num [sourceEffective, scalarForm, scalarReturn, schurToyScale]
end Artform.Scores.GravityBridge.Native.Retrospective
