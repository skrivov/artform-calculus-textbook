import ArtformScores.GravityBridge.SourceRadicalDefs
/-! # Sources constrain the allowable radical quotient -/
namespace Artform.Scores.GravityBridge.Statement
/-- **GAC:source-radical-audit** (sources constrain the allowable radical quotient). -/
@[ledger "GAC:source-radical-audit"]
def sourceRadicalLaw : Prop :=
  (∀ (N : Submodule ℚ GaugeSpace) (j k : ℚ),
    (N ≤ gaugeNull ∧ ∃ Sq : GaugeSpace ⧸ N →ₗ[ℚ] ℚ,
      Sq.comp N.mkQ = visibleSource j + k • hiddenSource) ↔ N ≤ sourceCompatibleNull j k) ∧
  (∀ (j : ℚ),
    sourceCompatibleNull j 0 = gaugeNull) ∧
  (∀ (j k : ℚ) (_hk : k ≠ 0),
    sourceCompatibleNull j k = ⊥) ∧
  (∀ (j k : ℚ),
    ∃ Sq : GaugeSpace ⧸ sourceCompatibleNull j k →ₗ[ℚ] ℚ,
      Sq.comp (sourceCompatibleNull j k).mkQ = visibleSource j + k • hiddenSource) ∧
  (∀ (j k : ℚ),
    ∃ wq : LinearMap.BilinForm ℚ (GaugeSpace ⧸ sourceCompatibleNull j k),
      ∀ x y, wq ((sourceCompatibleNull j k).mkQ x) ((sourceCompatibleNull j k).mkQ y) =
        gaugeForm x y) ∧
  (∀ (j k : ℚ),
    sourceCompatibleNull j k ≤ (sourceCompatibleNull j k).comap gaugeStep) ∧
  (∀ (j k : ℚ) (_hk : k ≠ 0),
    ¬ ∃ (N : Submodule ℚ GaugeSpace) (wq : LinearMap.BilinForm ℚ (GaugeSpace ⧸ N))
      (Sq : GaugeSpace ⧸ N →ₗ[ℚ] ℚ),
      (∀ x y, wq (N.mkQ x) (N.mkQ y) = gaugeForm x y) ∧
      wq.Nondegenerate ∧ Sq.comp N.mkQ = visibleSource j + k • hiddenSource)
end Artform.Scores.GravityBridge.Statement
