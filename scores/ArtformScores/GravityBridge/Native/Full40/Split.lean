import ArtformScores.GravityBridge.Native.Full40.SplitStatements
/-! # The exact metric and coframe Lorentz isomorphism -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]
lemma coframe_reconstruction (F : Frame K) :
    coframeReconstruct (metricVariation F) (coframeLorentz F) = F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coframeReconstruct, metricVariation, coframeLorentz, frameGram, eta, lie] <;> ring
lemma reconstruction_metric (m : symmetricFrames (K := K)) (w : Biv K) :
    metricVariation (coframeReconstruct m.val w) = m.val := by
  ext i j
  have hs := m.property i j
  have hz := lie_metric_kernel w i j
  have he (a : Fin 4) : eta (K := K) a * eta a = 1 := by fin_cases a <;> norm_num [eta]
  simp only [metricVariation, coframeReconstruct, Matrix.add_apply, Matrix.smul_apply,
    frameGram, smul_eq_mul] at hz ⊢
  calc
    _ = ((eta i * eta i) * m.val i j + (eta j * eta j) * m.val j i) / 2 +
        (eta i * lie w i j + eta j * lie w j i) := by ring
    _ = m.val i j := by rw [he, he, ← hs]; simp only [hz]; ring
lemma reconstruction_lorentz (m : symmetricFrames (K := K)) (w : Biv K) :
    coframeLorentz (coframeReconstruct m.val w) = w := by
  funext a
  have hs := m.property
  fin_cases a <;>
    simp [coframeLorentz, coframeReconstruct, frameGram, eta, lie, ← hs 0 1,
      ← hs 0 2, ← hs 0 3, ← hs 2 3, ← hs 3 1, ← hs 1 2] <;> ring
noncomputable def coframeSplit : Frame K ≃ₗ[K] (symmetricFrames (K := K) × Biv K) where
  toFun := fun F => (metricReadout F, coframeLorentz F)
  invFun := fun z => coframeReconstruct z.1.val z.2
  left_inv := coframe_reconstruction
  right_inv := by
    intro z
    apply Prod.ext
    · apply Subtype.ext
      exact reconstruction_metric z.1 z.2
    · exact reconstruction_lorentz z.1 z.2
  map_add' := by
    intro F G
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      change metricVariation (F + G) i j = metricVariation F i j + metricVariation G i j
      simp [metricVariation]
      ring
    · ext a
      fin_cases a <;> simp [coframeLorentz] <;> ring
  map_smul' := by
    intro c F
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      change metricVariation (c • F) i j = c * metricVariation F i j
      simp [metricVariation]
      ring
    · ext a
      fin_cases a <;> simp [coframeLorentz] <;> ring
lemma coframe_linear_equiv : Nonempty (Frame K ≃ₗ[K] (symmetricFrames (K := K) × Biv K)) :=
  ⟨coframeSplit⟩
lemma split_readout_injective (F G : Frame K)
    (hm : metricVariation F = metricVariation G) (hw : coframeLorentz F = coframeLorentz G) :
    F = G := by
  rw [← coframe_reconstruction F, ← coframe_reconstruction G, hm, hw]
/-- **GAC2:metric-coframe-lorentz-isomorphism**
(the exact metric and coframe lorentz isomorphism). -/
@[ledger "GAC2:metric-coframe-lorentz-isomorphism"]
theorem splitLaw : Statement.splitLaw := by
  intro K _ _
  exact ⟨coframe_reconstruction,
    reconstruction_metric,
    reconstruction_lorentz,
    coframe_linear_equiv,
    split_readout_injective⟩
/-! ## Non-vacuity -/
example : metricVariation (coframeReconstruct (0 : Frame ℚ) ![1, 2, 3, 4, 5, 6]) = 0 ∧
    coframeLorentz (coframeReconstruct (0 : Frame ℚ) ![1, 2, 3, 4, 5, 6]) =
      ![1, 2, 3, 4, 5, 6] := by
  constructor
  · exact reconstruction_metric ⟨0, by intro i j; rfl⟩ _
  · exact reconstruction_lorentz ⟨0, by intro i j; rfl⟩ _
end Artform.Scores.GravityBridge.Native.Full40
