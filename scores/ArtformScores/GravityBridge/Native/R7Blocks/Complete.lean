import ArtformScores.GravityBridge.Native.R7Blocks.CompleteStatements

/-! # Complete bounded graph defect with its own propagator -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma block_defect_split (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) (y : Y) :
    blockAction A11 A12 A21 A22 (graphMap K y) =
      graphMap K (ownDataAction A11 A12 K y) + (0, blockDefect A11 A12 A21 A22 K y) := by
  apply Prod.ext
  · change A11 y + A12 (K y) = A11 y + A12 (K y) + 0
    simp
  · change A21 y + A22 (K y) = K (ownDataAction A11 A12 K y) +
      (A21 y + A22 (K y) - K (ownDataAction A11 A12 K y))
    abel

lemma invariant_image_iff_complete_defect (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) :
    Set.MapsTo (blockAction A11 A12 A21 A22) (Set.range (graphMap K))
      (Set.range (graphMap K)) ↔ blockDefect A11 A12 A21 A22 K = 0 := by
  constructor
  · intro h
    ext y
    rcases h (Set.mem_range_self y) with ⟨z, hz⟩
    have hf := congrArg Prod.fst hz
    have hs := congrArg Prod.snd hz
    change z = ownDataAction A11 A12 K y at hf
    change K z = A21 y + A22 (K y) at hs
    change A21 y + A22 (K y) - K (ownDataAction A11 A12 K y) = 0
    rw [← hf, hs, sub_self]
  · intro h
    rintro _ ⟨y, rfl⟩
    refine ⟨ownDataAction A11 A12 K y, ?_⟩
    apply Prod.ext
    · rfl
    · have hv := congrArg (fun F : Y →L[ℝ] Z => F y) h
      change A21 y + A22 (K y) - K (ownDataAction A11 A12 K y) = 0 at hv
      exact (sub_eq_zero.mp hv).symm

lemma complete_riccati_expansion (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) :
    blockDefect A11 A12 A21 A22 K =
      A21 + A22.comp K - K.comp A11 - (K.comp A12).comp K := by
  apply ContinuousLinearMap.ext
  intro y
  change A21 y + A22 (K y) - K (A11 y + A12 (K y)) =
    A21 y + A22 (K y) - K (A11 y) - K (A12 (K y))
  rw [map_add]
  abel

/-- **GAC2:complete-graph-riccati**
(complete bounded graph defect with its own propagator). -/
@[ledger "GAC2:complete-graph-riccati"]
theorem completeLaw : Statement.completeLaw := by
  intro Y Z _ _ _ _
  exact ⟨block_defect_split,
    invariant_image_iff_complete_defect,
    complete_riccati_expansion⟩

/-! ## Non-vacuity -/

example :
    blockDefect (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)
      (ContinuousLinearMap.id ℝ ℝ) 0 (ContinuousLinearMap.id ℝ ℝ) = 0 ∧
    blockDefect (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)
      (ContinuousLinearMap.id ℝ ℝ) 0 0 ≠ 0 := by
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    simp [blockDefect, ownDataAction]
  · intro h
    have hx := congrArg (fun F : ℝ →L[ℝ] ℝ => F 1) h
    norm_num [blockDefect, ownDataAction] at hx

end Artform.Scores.GravityBridge.Native.R7Blocks
