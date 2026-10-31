import ArtformScores.GravityBridge.RadicalDefs

/-! # Actual finite radical and reduced evolution -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:radical-reduction** (actual finite radical and reduced evolution). -/
@[ledger "GAC:radical-reduction"]
def radicalLaw : Prop :=
  (∀ x : GaugeSpace, x ∈ gaugeNull ↔ ∀ y, gaugeForm x y = 0) ∧
  (∀ x y : GaugeSpace, phaseForm (constraintEmbedding x) (constraintEmbedding y) = gaugeForm x y) ∧
  (∀ x : GaugeSpace, gaugeQuotientEquiv (gaugeNull.mkQ x) = gaugeRead x) ∧
  (∀ x y : GaugeSpace, singularRelation (constraintEmbedding x) (constraintEmbedding y) ↔
    gaugeRead y = reducedDrift (gaugeRead x)) ∧
  (∀ x : GaugeSpace ⧸ gaugeNull,
    gaugeQuotientEquiv (gaugeQuotientStep x) = reducedDrift (gaugeQuotientEquiv x)) ∧
  (∀ x y : GaugeSpace, gaugeForm x y = (gaugeRead x).1 * (gaugeRead y).2 -
    (gaugeRead x).2 * (gaugeRead y).1) ∧
  (∀ x y : ℚ × ℚ, (reducedDrift x).1 * (reducedDrift y).2 -
    (reducedDrift x).2 * (reducedDrift y).1 = x.1 * y.2 - x.2 * y.1) ∧
  (∀ j : ℚ, ∃ Sq : GaugeSpace ⧸ gaugeNull →ₗ[ℚ] ℚ,
    Sq.comp gaugeNull.mkQ = visibleSource j) ∧
  (¬ ∃ Sq : GaugeSpace ⧸ gaugeNull →ₗ[ℚ] ℚ, Sq.comp gaugeNull.mkQ = hiddenSource)

end Artform.Scores.GravityBridge.Statement
