import ArtformScores.GravityBridge.Native.NativeCurrent.RadicalStatements

/-! # Admitted source-restricted current radical -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma radical_membership (W : Submodule K V) (B : V →ₗ[K] V →ₗ[K] K) (g : V) :
    g ∈ admittedRadical W B ↔ g ∈ W ∧ ∀ w ∈ W, B g w = 0 := Iff.rfl

lemma admitted_radical_generator_invariance (W : Submodule K V)
    (B : V →ₗ[K] V →ₗ[K] K) (A : Module.End K V)
    (hW : ∀ w ∈ W, A w ∈ W)
    (hconserve : ∀ g ∈ W, ∀ w ∈ W, B (A g) w + B g (A w) = 0) :
    ∀ g ∈ admittedRadical W B, A g ∈ admittedRadical W B := by
  intro g hg
  refine ⟨hW g hg.1, ?_⟩
  intro w hw
  have he := hconserve g hg.1 w hw
  rw [hg.2 (A w) (hW w hw), add_zero] at he
  exact he

lemma no_selected_radical_with_left_inverse (W : Submodule K V)
    (B : V →ₗ[K] V →ₗ[K] K)
    (hnondeg : ∀ g ∈ W, (∀ w ∈ W, B g w = 0) → g = 0) : admittedRadical W B = ⊥ := by
  apply le_antisymm
  · intro g hg
    exact (Submodule.mem_bot K).mpr (hnondeg g hg.1 hg.2)
  · exact bot_le

lemma source_restricted_radical (W : Submodule K V) (B : V →ₗ[K] V →ₗ[K] K)
    (J : Module.End K V) (g : V) :
    g ∈ admittedRadical (W⊓J.ker) B ↔
      g ∈ W ∧ J g = 0 ∧ ∀ w, w ∈ W → J w = 0 → B g w = 0 := by
  simp only [radical_membership, Submodule.mem_inf, LinearMap.mem_ker]
  aesop

/-- **GAC2:admitted-source-current-radical**
(admitted source-restricted current radical). -/
@[ledger "GAC2:admitted-source-current-radical"]
theorem radicalLaw : Statement.radicalLaw := by
  intro K V _ _ _
  exact ⟨radical_membership,
    admitted_radical_generator_invariance,
    no_selected_radical_with_left_inverse,
    source_restricted_radical⟩

/-! ## Non-vacuity -/

example : admittedRadical (⊤ : Submodule ℚ ℚ) (0 : ℚ →ₗ[ℚ] ℚ →ₗ[ℚ] ℚ) = ⊤ := by
  ext g
  simp [radical_membership]

end Artform.Scores.GravityBridge.Native.NativeCurrent
