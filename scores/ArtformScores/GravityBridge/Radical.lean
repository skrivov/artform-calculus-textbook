import ArtformScores.GravityBridge.RadicalStatements
import ArtformScores.GravityBridge.Canonical
import ArtformScores.Rules

/-! # The singular action radical quotient is the old reduced move -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma constraint_form_pullback (x y : GaugeSpace) :
    phaseForm (constraintEmbedding x) (constraintEmbedding y) = gaugeForm x y := by
  rw [phaseForm_apply]
  simp [constraintEmbedding, boundaryPair, gaugeForm]

lemma gauge_quotient_read (x : GaugeSpace) :
    gaugeQuotientEquiv (gaugeNull.mkQ x) = gaugeRead x := rfl

lemma gauge_radical (x : GaugeSpace) :
    x ∈ gaugeNull ↔ ∀ y, gaugeForm x y = 0 := by
  constructor
  · rintro ⟨hq, hp⟩ y
    simp [gaugeForm, hq, hp]
  · intro h
    have hq := h (0, 1, 0)
    have hp := h (1, 0, 0)
    change x.1 = 0 ∧ x.2.1 = 0
    norm_num [gaugeForm] at hq hp
    exact ⟨hq, hp⟩

lemma constrained_relation_reduces (x y : GaugeSpace) :
    singularRelation (constraintEmbedding x) (constraintEmbedding y) ↔
      gaugeRead y = reducedDrift (gaugeRead x) := by
  rw [singular_relation_iff]
  simp [constraintEmbedding, gaugeRead, reducedDrift, Prod.ext_iff, and_comm]

lemma reduction_form (x y : GaugeSpace) :
    gaugeForm x y = (gaugeRead x).1 * (gaugeRead y).2 -
      (gaugeRead x).2 * (gaugeRead y).1 := rfl

lemma reduced_drift_form (x y : ℚ × ℚ) :
    (reducedDrift x).1 * (reducedDrift y).2 -
      (reducedDrift x).2 * (reducedDrift y).1 = x.1 * y.2 - x.2 * y.1 := by
  dsimp [reducedDrift]
  ring

lemma gauge_source_quotient (j : ℚ) :
    ∃ Sq : GaugeSpace ⧸ gaugeNull →ₗ[ℚ] ℚ, Sq.comp gaugeNull.mkQ = visibleSource j := by
  apply (output_descends_iff gaugeNull (visibleSource j)).mpr
  intro x hx
  change x.1 = 0 ∧ x.2.1 = 0 at hx
  change j * x.1 = 0
  simp [hx.1]

lemma quotient_step_drift (x : GaugeSpace ⧸ gaugeNull) :
    gaugeQuotientEquiv (gaugeQuotientStep x) = reducedDrift (gaugeQuotientEquiv x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change gaugeQuotientEquiv (gaugeNull.mkQ (gaugeStep x)) =
      reducedDrift (gaugeQuotientEquiv (gaugeNull.mkQ x))
    rw [gauge_quotient_read, gauge_quotient_read]
    rfl

lemma hidden_source_not_quotient :
    ¬ ∃ Sq : GaugeSpace ⧸ gaugeNull →ₗ[ℚ] ℚ, Sq.comp gaugeNull.mkQ = hiddenSource := by
  intro h
  have hn := (output_descends_iff gaugeNull hiddenSource).mp h
  have hc := hn (show (0, 0, (1 : ℚ)) ∈ gaugeNull by simp [gaugeNull])
  norm_num [LinearMap.mem_ker, hiddenSource] at hc

/-- **GAC:radical-reduction** (the actual finite constrained form and quotient dynamics). -/
@[ledger "GAC:radical-reduction"]
theorem radicalLaw : Statement.radicalLaw := by
  exact ⟨gauge_radical, constraint_form_pullback, gauge_quotient_read,
    constrained_relation_reduces, quotient_step_drift, reduction_form, reduced_drift_form,
    gauge_source_quotient, hidden_source_not_quotient⟩

/-! ## Non-vacuity -/

example (x : ℚ × ℚ) :
    Matrix.mulVec (realize [Step.move (1 : ℚ)] : Matrix (Fin 2) (Fin 2) ℚ) ![x.1, x.2] =
      ![(reducedDrift x).1, (reducedDrift x).2] := by
  ext i
  fin_cases i <;>
    simp [realize, Step.mat, reducedDrift, Matrix.mulVec, dotProduct, Fin.sum_univ_two]


example : singularRelation (constraintEmbedding (1, 2, 7))
    (constraintEmbedding (3, 2, 99)) := by
  rw [constrained_relation_reduces]
  norm_num [gaugeRead, reducedDrift]

example : (1, 2, 7) ≠ (1, 2, 99) ∧
    gaugeNull.mkQ (1, 2, 7) = gaugeNull.mkQ (1, 2, 99) := by
  constructor
  · norm_num
  · apply gaugeQuotientEquiv.injective
    rw [gauge_quotient_read, gauge_quotient_read]
    rfl

end

end Artform.Scores.GravityBridge
