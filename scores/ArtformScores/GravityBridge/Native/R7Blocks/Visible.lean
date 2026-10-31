import ArtformScores.GravityBridge.Native.R7Blocks.VisibleStatements

/-! # Artform visible closure and complete image invariance -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma visible_closure_always (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) (y : Y) :
    (blockRealization K).visible (blockAction A11 A12 A21 A22) y =
      ownDataAction A11 A12 K y := rfl

lemma artform_complete_defect (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) :
    linearDefect (graphMap K) (ContinuousLinearMap.fst ℝ Y Z)
      (blockAction A11 A12 A21 A22) =
      (0 : Y →L[ℝ] Y).prod (blockDefect A11 A12 A21 A22 K) := by
  apply ContinuousLinearMap.ext
  intro y
  apply Prod.ext
  · change A11 y + A12 (K y) - (A11 y + A12 (K y)) = 0
    exact sub_self _
  · rfl

lemma artform_intertwining_iff_riccati (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) :
    (blockRealization K).Intertwines (blockAction A11 A12 A21 A22) ↔
      blockDefect A11 A12 A21 A22 K = 0 := by
  rw [← invariant_iff_intertwines]
  have hi := invariant_image_iff_complete_defect A11 A12 A21 A22 K
  constructor
  · intro h
    apply hi.mp
    rintro _ ⟨y, rfl⟩
    exact h y
  · intro h y
    exact hi.mpr h (Set.mem_range_self y)

lemma source_witness_leak (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (y : Y) (phi : Z →L[ℝ] ℝ)
    (hsource : phi (A21 y) = 36 / 505) :
    ¬ (blockRealization (0 : Y →L[ℝ] Z)).Invariant (blockAction A11 A12 A21 A22) := by
  intro h
  have hz := (artform_intertwining_iff_riccati A11 A12 A21 A22 0).mp
    ((invariant_iff_intertwines _ _).mp h)
  have hh := congrArg (fun F : Y →L[ℝ] Z => phi (F y)) hz
  simp only [blockDefect, ownDataAction, ContinuousLinearMap.comp_zero,
    add_zero, ContinuousLinearMap.zero_comp, sub_zero] at hh
  rw [hsource] at hh
  norm_num at hh

/-- **GAC2:visible-closure-image-gap**
(artform visible closure and complete image invariance). -/
@[ledger "GAC2:visible-closure-image-gap"]
theorem visibleLaw : Statement.visibleLaw := by
  intro Y Z _ _ _ _
  exact ⟨visible_closure_always,
    artform_complete_defect,
    artform_intertwining_iff_riccati,
    source_witness_leak⟩

/-! ## Non-vacuity -/

example : (blockRealization (0 : ℝ →L[ℝ] ℝ)).visible
    (blockAction 0 0 ((36 / 505 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 0) 1 = 0 ∧
    ¬ (blockRealization (0 : ℝ →L[ℝ] ℝ)).Invariant
      (blockAction 0 0 ((36 / 505 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 0) := by
  constructor
  · norm_num [blockRealization, Realization.visible, blockAction, graphMap]
  · apply source_witness_leak _ _ _ _ 1 (ContinuousLinearMap.id ℝ ℝ)
    norm_num

end Artform.Scores.GravityBridge.Native.R7Blocks
