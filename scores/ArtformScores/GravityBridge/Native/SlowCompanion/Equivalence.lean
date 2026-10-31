import ArtformScores.GravityBridge.Native.SlowCompanion.EquivalenceStatements

/-! # Admitted source and observation agreement -/

namespace Artform.Scores.GravityBridge.Native.SlowCompanion

variable {K H S O F : Type*} [Field K] [AddCommGroup H] [Module K H]
  [AddCommGroup S] [Module K S] [AddCommGroup O] [Module K O]
  [AddCommGroup F] [Module K F]

lemma complete_response_equivalence (W : Submodule K H) (J : H →ₗ[K] F)
    (read : H →ₗ[K] O) (U V : S →ₗ[K] H) (hU : ∀ s, U s ∈ W) :
    (∀ s, V s ∈ W ∧ J (V s) = J (U s) ∧ read (V s) = read (U s)) ↔
      ∀ s, (V - U) s ∈ compatibleChanges W J read := by
  constructor
  · intro h s
    rcases h s with ⟨hw, hj, hr⟩
    change (V s - U s ∈ W ∧ J (V s - U s) = 0) ∧ read (V s - U s) = 0
    exact ⟨⟨W.sub_mem hw (hU s), by rw [map_sub, hj, sub_self]⟩,
      by rw [map_sub, hr, sub_self]⟩
  · intro h s
    have hv := h s
    change (V s - U s ∈ W ∧ J (V s - U s) = 0) ∧ read (V s - U s) = 0 at hv
    refine ⟨?_, ?_, ?_⟩
    · have hw := W.add_mem hv.1.1 (hU s)
      simpa only [sub_add_cancel] using hw
    · exact sub_eq_zero.mp (by simpa only [map_sub] using hv.1.2)
    · exact sub_eq_zero.mp (by simpa only [map_sub] using hv.2)

lemma full_trace_rigidity (W : Submodule K H) (trace : H →ₗ[K] S)
    (recover : S →ₗ[K] H) (hrec : ∀ w ∈ W, recover (trace w) = w)
    (U V : O →ₗ[K] H) (hU : ∀ s, U s ∈ W) (hV : ∀ s, V s ∈ W)
    (htrace : trace.comp U = trace.comp V) : U = V := by
  ext s
  have ht := congrArg (fun f : O →ₗ[K] S => recover (f s)) htrace
  change recover (trace (U s)) = recover (trace (V s)) at ht
  rwa [hrec (U s) (hU s), hrec (V s) (hV s)] at ht

lemma invisible_read_can_change_force :
    (LinearMap.fst ℚ ℚ ℚ) (0, 1) = 0 ∧
    (LinearMap.snd ℚ ℚ ℚ) (0, 1) ≠ 0 := by norm_num

/-- **GAC2:source-observation-preparation-equivalence**
(admitted source and observation agreement). -/
@[ledger "GAC2:source-observation-preparation-equivalence"]
theorem equivalenceLaw : Statement.equivalenceLaw := by
  intro K H S O F _ _ _ _ _ _ _ _ _
  exact ⟨complete_response_equivalence,
    full_trace_rigidity,
    invisible_read_can_change_force⟩

/-! ## Non-vacuity -/

example : compatibleChanges (⊤ : Submodule ℚ (ℚ × ℚ))
    (LinearMap.snd ℚ ℚ ℚ) (LinearMap.fst ℚ ℚ ℚ) = ⊥ := by
  ext x
  simp only [compatibleChanges, Submodule.mem_inf, Submodule.mem_top, LinearMap.mem_ker,
    LinearMap.fst_apply, LinearMap.snd_apply, Submodule.mem_bot, true_and]
  exact ⟨fun h => Prod.ext h.2 h.1, fun h => by simp [h]⟩

end Artform.Scores.GravityBridge.Native.SlowCompanion
