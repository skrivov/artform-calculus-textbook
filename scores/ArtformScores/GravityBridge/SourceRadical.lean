import ArtformScores.GravityBridge.SourceRadicalStatements
/-! # Sources constrain the allowable radical quotient -/
namespace Artform.Scores.GravityBridge
noncomputable section
lemma maximal_source_compatible_null (N : Submodule ℚ GaugeSpace) (j k : ℚ) :
    (N ≤ gaugeNull ∧ ∃ Sq : GaugeSpace ⧸ N →ₗ[ℚ] ℚ,
      Sq.comp N.mkQ = visibleSource j + k • hiddenSource) ↔ N ≤ sourceCompatibleNull j k := by
  rw [output_descends_iff]
  exact le_inf_iff.symm
lemma source_compatible_null_zero (j : ℚ) : sourceCompatibleNull j 0 = gaugeNull := by
  ext x
  change (x ∈ gaugeNull ∧ (visibleSource j + (0 : ℚ) • hiddenSource) x = 0) ↔ x ∈ gaugeNull
  constructor
  · exact And.left
  · intro hx
    refine ⟨hx, ?_⟩
    change x.1 = 0 ∧ x.2.1 = 0 at hx
    simp [visibleSource, hx.1]
lemma source_compatible_null_nonzero (j k : ℚ) (hk : k ≠ 0) :
    sourceCompatibleNull j k = ⊥ := by
  ext x
  change (x ∈ gaugeNull ∧ (visibleSource j + k • hiddenSource) x = 0) ↔ x = 0
  constructor
  · rintro ⟨hx, hs⟩
    change x.1 = 0 ∧ x.2.1 = 0 at hx
    have hg : x.2.2 = 0 := by
      change j * x.1 + k * x.2.2 = 0 at hs
      rw [hx.1, mul_zero, zero_add] at hs
      exact (mul_eq_zero.mp hs).resolve_left hk
    exact Prod.ext hx.1 (Prod.ext hx.2 hg)
  · rintro rfl
    simp
lemma compatible_source_exists (j k : ℚ) :
    ∃ Sq : GaugeSpace ⧸ sourceCompatibleNull j k →ₗ[ℚ] ℚ,
      Sq.comp (sourceCompatibleNull j k).mkQ = visibleSource j + k • hiddenSource := by
  exact (output_descends_iff _ _).mpr inf_le_right
lemma compatible_form_exists (j k : ℚ) :
    ∃ wq : LinearMap.BilinForm ℚ (GaugeSpace ⧸ sourceCompatibleNull j k),
      ∀ x y, wq ((sourceCompatibleNull j k).mkQ x) ((sourceCompatibleNull j k).mkQ y) =
        gaugeForm x y := by
  apply (bilinear_descends_iff _ _).mpr
  constructor
  · intro n hn x
    have hN : n ∈ gaugeNull := hn.1
    change n.1 = 0 ∧ n.2.1 = 0 at hN
    simp [gaugeForm, hN.1, hN.2]
  · intro n hn x
    have hN : n ∈ gaugeNull := hn.1
    change n.1 = 0 ∧ n.2.1 = 0 at hN
    simp [gaugeForm, hN.1, hN.2]
lemma compatible_step (j k : ℚ) :
    sourceCompatibleNull j k ≤ (sourceCompatibleNull j k).comap gaugeStep := by
  by_cases hk : k = 0
  · subst k
    rw [source_compatible_null_zero]
    exact gauge_step_preserves
  · rw [source_compatible_null_nonzero j k hk]
    exact bot_le
lemma source_forbids_nondegenerate (j k : ℚ) (hk : k ≠ 0) :
    ¬ ∃ (N : Submodule ℚ GaugeSpace) (wq : LinearMap.BilinForm ℚ (GaugeSpace ⧸ N))
      (Sq : GaugeSpace ⧸ N →ₗ[ℚ] ℚ),
      (∀ x y, wq (N.mkQ x) (N.mkQ y) = gaugeForm x y) ∧
      wq.Nondegenerate ∧ Sq.comp N.mkQ = visibleSource j + k • hiddenSource := by
  rintro ⟨N, wq, Sq, hform, hnd, hsource⟩
  let g : GaugeSpace := (0, 0, 1)
  have hg : N.mkQ g = 0 := by
    apply hnd.1
    intro v
    refine Submodule.Quotient.induction_on N v (fun x => ?_)
    change wq (N.mkQ g) (N.mkQ x) = 0
    rw [hform]
    norm_num [g, gaugeForm]
  have hs := LinearMap.congr_fun hsource g
  change Sq (N.mkQ g) = j * g.1 + k * g.2.2 at hs
  rw [hg, map_zero] at hs
  norm_num [g] at hs
  exact hk hs.symm
/-- **GAC:source-radical-audit** (sources constrain the allowable radical quotient). -/
@[ledger "GAC:source-radical-audit"]
theorem sourceRadicalLaw : Statement.sourceRadicalLaw := by
  exact ⟨maximal_source_compatible_null,
    source_compatible_null_zero,
    source_compatible_null_nonzero,
    compatible_source_exists,
    compatible_form_exists,
    compatible_step,
    source_forbids_nondegenerate⟩
/-! ## Non-vacuity -/
example : sourceCompatibleNull 7 0 = gaugeNull ∧ sourceCompatibleNull 7 1 = ⊥ :=
  ⟨source_compatible_null_zero 7, source_compatible_null_nonzero 7 1 (by norm_num)⟩
end
end Artform.Scores.GravityBridge
