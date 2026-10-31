import ArtformScores.GravityBridge.Native.R7Blocks.NativeStepStatements

/-! # Single-step invariance in the original Hilbert norm -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma hilbert_projection_data (W : Submodule ℝ H) [W.HasOrthogonalProjection] :
    W.starProjection * W.starProjection = W.starProjection ∧
    ‖W.starProjection‖ ≤ 1 ∧ ‖(1 : H →L[ℝ] H) - W.starProjection‖ ≤ 1 := by
  refine ⟨W.isIdempotentElem_starProjection, W.starProjection_norm_le, ?_⟩
  rw [← W.starProjection_orthogonal']
  exact Wᗮ.starProjection_norm_le

omit [CompleteSpace H] in
lemma complete_image_offblock_iff (W : Submodule ℝ H) [W.HasOrthogonalProjection]
    (T : H →L[ℝ] H) :
    (∀ y ∈ W, T y ∈ W) ↔ ((1 : H →L[ℝ] H) - W.starProjection) * T * W.starProjection = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    change T (W.starProjection x) - W.starProjection (T (W.starProjection x)) = 0
    exact sub_eq_zero.mpr (W.starProjection_eq_self_iff.mpr
      (h _ (W.starProjection_apply_mem x))).symm
  · intro h y hy
    have he := congrArg (fun F : H →L[ℝ] H => F y) h
    have hp : W.starProjection y = y := W.starProjection_eq_self_iff.mpr hy
    change T (W.starProjection y) - W.starProjection (T (W.starProjection y)) = 0 at he
    rw [hp] at he
    exact W.starProjection_eq_self_iff.mp (sub_eq_zero.mp he).symm

lemma hilbert_one_step_implies_generator (W : Submodule ℝ H) [W.HasOrthogonalProjection]
    (A : H →L[ℝ] H) (h a : ℝ) (hh : 0 < h) (hA : ‖A‖ ≤ a)
    (hsmall : Real.exp (h * a) - 1 < 1)
    (hstep : ∀ y ∈ W, NormedSpace.exp (h • A) y ∈ W) : ∀ y ∈ W, A y ∈ W := by
  cases subsingleton_or_nontrivial H with
  | inl hH =>
    have := hH
    intro y _
    simpa only [Subsingleton.elim (A y) 0] using W.zero_mem
  | inr hH =>
    have := hH
    have hp := hilbert_projection_data W
    have hz := (complete_image_offblock_iff W (NormedSpace.exp (h • A))).mp hstep
    exact (complete_image_offblock_iff W A).mpr
      (one_step_offblock_implies_generator W.starProjection A h a hh hp.1 hp.2.1 hp.2.2
        hA hsmall hz)

lemma closed_hilbert_one_step_implies_generator (W : Submodule ℝ H)
    (hclosed : IsClosed (W : Set H))
    (A : H →L[ℝ] H) (h a : ℝ) (hh : 0 < h) (hA : ‖A‖ ≤ a)
    (hsmall : Real.exp (h * a) - 1 < 1)
    (hstep : ∀ y ∈ W, NormedSpace.exp (h • A) y ∈ W) : ∀ y ∈ W, A y ∈ W := by
  have : IsClosed (W : Set H) := hclosed
  exact hilbert_one_step_implies_generator W A h a hh hA hsmall hstep

lemma graph_equation_one_step_implies_generator
    {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : H →L[ℝ] Y) (R : H →L[ℝ] Z) (K : Y →L[ℝ] Z)
    (A : H →L[ℝ] H) (h a : ℝ) (hh : 0 < h) (hA : ‖A‖ ≤ a)
    (hsmall : Real.exp (h * a) - 1 < 1)
    (hstep : ∀ w, R w = K (Q w) →
      R (NormedSpace.exp (h • A) w) = K (Q (NormedSpace.exp (h • A) w))) :
    ∀ w, R w = K (Q w) → R (A w) = K (Q (A w)) := by
  let W : Submodule ℝ H := (R - K.comp Q).ker
  have hc : IsClosed (W : Set H) := (R - K.comp Q).isClosed_ker
  have hm (w : H) : w ∈ W ↔ R w = K (Q w) := by
    change R w - K (Q w) = 0 ↔ _
    exact sub_eq_zero
  have hs : ∀ w ∈ W, NormedSpace.exp (h • A) w ∈ W := by
    intro w hw
    exact (hm _).mpr (hstep w ((hm w).mp hw))
  have hg := closed_hilbert_one_step_implies_generator W hc A h a hh hA hsmall hs
  intro w hw
  exact (hm _).mp (hg w ((hm w).mpr hw))

/-- **GAC2:hilbert-single-step-generator**
(single-step invariance in the original hilbert norm). -/
@[ledger "GAC2:hilbert-single-step-generator"]
theorem nativeStepLaw : Statement.nativeStepLaw := by
  intro H _ _ _
  exact ⟨hilbert_projection_data,
    complete_image_offblock_iff,
    hilbert_one_step_implies_generator,
    closed_hilbert_one_step_implies_generator,
    graph_equation_one_step_implies_generator⟩

/-! ## Non-vacuity -/

example : ∀ y ∈ (⊤ : Submodule ℝ ℝ), (0 : ℝ →L[ℝ] ℝ) y ∈ (⊤ : Submodule ℝ ℝ) := by
  apply closed_hilbert_one_step_implies_generator (⊤ : Submodule ℝ ℝ) isClosed_univ
    (0 : ℝ →L[ℝ] ℝ) 1 0
  all_goals simp

end Artform.Scores.GravityBridge.Native.R7Blocks
