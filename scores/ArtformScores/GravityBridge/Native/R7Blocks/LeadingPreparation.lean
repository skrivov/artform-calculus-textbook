import ArtformScores.GravityBridge.Native.R7Blocks.LeadingPreparationStatements

/-! # The leading prepared graph requires a changed trace -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks

variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma triangular_graph_criterion (S : Y →L[ℝ] Y) (N : Z →L[ℝ] Z)
    (F K : Y →L[ℝ] Z) :
    blockDefect S 0 F N K = 0 ↔ K.comp S - N.comp K = F := by
  have he : blockDefect S 0 F N K = F - (K.comp S - N.comp K) := by
    ext y
    simp [blockDefect, ownDataAction]
    abel
  rw [he, sub_eq_zero]
  exact eq_comm

lemma leading_preparation_lower_bound (S : Y →L[ℝ] Y) (N : Z →L[ℝ] Z)
    (F K : Y →L[ℝ] Z) (a d : ℝ) (ha : 0 < a) (hw : d ≤ ‖F‖)
    (hS : ‖S‖ ≤ a) (hN : ‖N‖ ≤ a) (hK : K.comp S - N.comp K = F) :
    d / (2 * a) ≤ ‖K‖ := by
  apply (div_le_iff₀ (show 0 < 2 * a by positivity)).2
  have hb : ‖F‖ ≤ 2 * a * ‖K‖ := by
    rw [← hK]
    calc
      _ ≤ ‖K.comp S‖ + ‖N.comp K‖ := norm_sub_le _ _
      _ ≤ ‖K‖ * ‖S‖ + ‖N‖ * ‖K‖ := by
        gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖K‖ * a + a * ‖K‖ := by gcongr
      _ = 2 * a * ‖K‖ := by ring
  nlinarith

lemma zero_coordinate_copy_invariant_iff (S : Y →L[ℝ] Y) (N : Z →L[ℝ] Z)
    (F : Y →L[ℝ] Z) :
    Set.MapsTo (blockAction S 0 F N) (Set.range (graphMap (0 : Y →L[ℝ] Z)))
      (Set.range (graphMap (0 : Y →L[ℝ] Z))) ↔ F = 0 := by
  rw [invariant_image_iff_complete_defect]
  simp [blockDefect, ownDataAction]

lemma prepared_graph_cannot_copy_zero_trace (r : ℝ) (S : Y →L[ℝ] Y)
    (N L : Z →L[ℝ] Z) (F : Y →L[ℝ] Z)
    (hS : S.comp S = (-r) • ContinuousLinearMap.id ℝ Y)
    (hLB : L.comp (quadraticResolvent r N) = ContinuousLinearMap.id ℝ Z)
    (hBL : (quadraticResolvent r N).comp L = ContinuousLinearMap.id ℝ Z)
    (hF : F ≠ 0) : quadraticSylvester S N L F ≠ 0 := by
  intro hz
  have he := quadratic_sylvester_solves r S N L F hS hLB hBL
  rw [hz] at he
  simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, sub_zero] at he
  exact hF he.symm

/-- **GAC2:leading-preparation-trace-gap**
(the leading prepared graph requires a changed trace). -/
@[ledger "GAC2:leading-preparation-trace-gap"]
theorem leadingPreparationLaw : Statement.leadingPreparationLaw := by
  intro Y Z _ _ _ _
  exact ⟨triangular_graph_criterion,
    leading_preparation_lower_bound,
    zero_coordinate_copy_invariant_iff,
    prepared_graph_cannot_copy_zero_trace⟩

/-! ## Non-vacuity -/

example : quadraticSylvester referenceOscillator 0 referenceInverse referenceForcing ≠ 0 := by
  apply prepared_graph_cannot_copy_zero_trace 14 referenceOscillator 0 referenceInverse
    referenceForcing reference_sylvester_hypotheses.1
    reference_sylvester_hypotheses.2.1 reference_sylvester_hypotheses.2.2
  intro h
  have hz := congrArg (fun F : (ℝ × ℝ) →L[ℝ] ℝ => F (1, 0)) h
  norm_num [referenceForcing] at hz

end Artform.Scores.GravityBridge.Native.R7Blocks
