import ArtformScores.GravityBridge.Statements

/-! # Quantitative changes of an embedded realization -/

namespace Artform.Scores.GravityBridge

section Estimate

variable {Y H : Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem linearDefect_sub (E F : Y →L[ℝ] H) (R : H →L[ℝ] Y) (T : H →L[ℝ] H) :
    linearDefect F R T - linearDefect E R T =
      T.comp (F - E) - (F - E).comp (R.comp (T.comp F)) -
        E.comp (R.comp (T.comp (F - E))) := by
  ext y
  simp only [linearDefect, sub_apply, ContinuousLinearMap.comp_apply,
    map_sub]
  abel

theorem linearDefect_norm_sub_le (E F : Y →L[ℝ] H)
    (R : H →L[ℝ] Y) (T : H →L[ℝ] H) :
    ‖linearDefect F R T - linearDefect E R T‖ ≤
      ‖T‖ * ‖F - E‖ * (1 + ‖R‖ * (‖E‖ + ‖F‖)) := by
  have hfirst := T.opNorm_comp_le (F - E)
  have hsecond : ‖(F - E).comp (R.comp (T.comp F))‖ ≤
      ‖F - E‖ * (‖R‖ * (‖T‖ * ‖F‖)) := by
    calc
      _ ≤ ‖F - E‖ * ‖R.comp (T.comp F)‖ := (F - E).opNorm_comp_le _
      _ ≤ ‖F - E‖ * (‖R‖ * ‖T.comp F‖) :=
        mul_le_mul_of_nonneg_left (R.opNorm_comp_le _) (norm_nonneg _)
      _ ≤ ‖F - E‖ * (‖R‖ * (‖T‖ * ‖F‖)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (T.opNorm_comp_le _) (norm_nonneg _)
  have hthird : ‖E.comp (R.comp (T.comp (F - E)))‖ ≤
      ‖E‖ * (‖R‖ * (‖T‖ * ‖F - E‖)) := by
    calc
      _ ≤ ‖E‖ * ‖R.comp (T.comp (F - E))‖ := E.opNorm_comp_le _
      _ ≤ ‖E‖ * (‖R‖ * ‖T.comp (F - E)‖) :=
        mul_le_mul_of_nonneg_left (R.opNorm_comp_le _) (norm_nonneg _)
      _ ≤ ‖E‖ * (‖R‖ * (‖T‖ * ‖F - E‖)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (T.opNorm_comp_le _) (norm_nonneg _)
  rw [linearDefect_sub]
  calc
    _ ≤ ‖T.comp (F - E) - (F - E).comp (R.comp (T.comp F))‖ +
        ‖E.comp (R.comp (T.comp (F - E)))‖ := norm_sub_le _ _
    _ ≤ ‖T.comp (F - E)‖ + ‖(F - E).comp (R.comp (T.comp F))‖ +
        ‖E.comp (R.comp (T.comp (F - E)))‖ :=
      add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ ‖T‖ * ‖F - E‖ + ‖F - E‖ * (‖R‖ * (‖T‖ * ‖F‖)) +
        ‖E‖ * (‖R‖ * (‖T‖ * ‖F - E‖)) :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = ‖T‖ * ‖F - E‖ * (1 + ‖R‖ * (‖E‖ + ‖F‖)) := by ring

/-- A strictly smaller perturbation bound cannot remove a known nonzero defect. -/
theorem defect_gap_obstruction (E F : Y →L[ℝ] H) (R : H →L[ℝ] Y)
    (T : H →L[ℝ] H) (d : ℝ) (hd : d ≤ ‖linearDefect E R T‖)
    (hsmall : ‖T‖ * ‖F - E‖ * (1 + ‖R‖ * (‖E‖ + ‖F‖)) < d) :
    linearDefect F R T ≠ 0 := by
  intro h
  have hb := linearDefect_norm_sub_le E F R T
  rw [h, zero_sub, norm_neg] at hb
  exact (not_le_of_gt hsmall) (hd.trans hb)

end Estimate

/-- **GAC:defect-stability** (quantitative stability of the full realization defect). -/
@[ledger "GAC:defect-stability"]
theorem defectStability : Statement.defectStability := by
  intro Y H _ _ _ _ E F R T
  exact linearDefect_norm_sub_le E F R T

/-! ## Non-vacuity -/

/-- Common readout, original embedding and a different graph embedding. -/
def normRead : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

def normEmbed : ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.id ℝ ℝ).prod 0

def normRepaired : ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ)

def normStep : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- A changed graph can be invariant although the old graph is not, with the
same exact readout on both. The stability estimate applies to this genuine change. -/
example :
    normRead.comp normEmbed = ContinuousLinearMap.id ℝ ℝ ∧
    normRead.comp normRepaired = ContinuousLinearMap.id ℝ ℝ ∧
    linearDefect normRepaired normRead normStep = 0 ∧
    linearDefect normEmbed normRead normStep ≠ 0 := by
  refine ⟨by ext; rfl, by ext; rfl, ?_, ?_⟩
  · ext <;> simp [linearDefect, normRead, normRepaired, normStep]
  · intro h
    have hy := congrArg (fun f : ℝ →L[ℝ] ℝ × ℝ => (f 1).2) h
    norm_num [linearDefect, normRead, normEmbed, normStep] at hy

example :
    ‖linearDefect normRepaired normRead normStep -
        linearDefect normEmbed normRead normStep‖ ≤
      ‖normStep‖ * ‖normRepaired - normEmbed‖ *
        (1 + ‖normRead‖ * (‖normEmbed‖ + ‖normRepaired‖)) :=
  linearDefect_norm_sub_le _ _ _ _

end Artform.Scores.GravityBridge
