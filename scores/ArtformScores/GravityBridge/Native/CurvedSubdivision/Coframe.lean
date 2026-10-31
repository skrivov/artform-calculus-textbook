import ArtformScores.GravityBridge.Native.CurvedSubdivision.CoframeStatements

/-! # Coframe source retained after connection detail stationarity -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40



open Filter
noncomputable section

lemma stationary_value_coframe_derivative (b c s : ℝ) :
    HasDerivAt (fun x => stationaryValue x c s)
      ((1 / 101 : ℝ) - Real.sqrt (detailD c s)) b := by
  convert (((hasDerivAt_id b).const_mul (1 / 101 : ℝ)).sub
    ((hasDerivAt_id b).mul_const (Real.sqrt (detailD c s)))) using 1
  · rfl
  · ring

lemma literal_stationary_coframe_derivative (b u r : ℝ) (hb : b ≠ 0) (hu : 0 < u)
    (hrc : Real.cosh r = stationaryC (Real.cosh u) (Real.sinh u))
    (hrs : Real.sinh r = stationaryS (Real.cosh u) (Real.sinh u)) :
    HasDerivAt (fun x => literalTwoChildAction x u r)
      ((1 / 101 : ℝ) - Real.sqrt (detailD (Real.cosh u) (Real.sinh u))) b := by
  have hs := Real.sinh_pos_iff.mpr hu
  have hc := Real.cosh_sq_sub_sinh_sq u
  have hco : 1 < Real.cosh u := by
    nlinarith [Real.one_le_cosh u, mul_pos hs hs]
  have heq : (fun x => literalTwoChildAction x u r) =ᶠ[nhds b]
      (fun x => stationaryValue x (Real.cosh u) (Real.sinh u)) := by
    filter_upwards [eventually_ne_nhds hb] with x hx
    have he := full_original_split_source_binding x u r 0 hx
    simp only [zero_mul, sub_zero] at he
    rw [he, actual_split_action_normal_form, zero_mul, sub_zero, hrc, hrs]
    exact (actual_stationary_current_return x (Real.cosh u) (Real.sinh u) hc hco hs).2.2
  exact (stationary_value_coframe_derivative b (Real.cosh u) (Real.sinh
    u)).congr_of_eventuallyEq heq

lemma connection_stationarity_retains_coframe_source (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∃ r : ℝ, nativeSplitFirst b u r 0 = 0 ∧
      HasDerivAt (fun x => literalTwoChildAction x u r)
        ((1 / 101 : ℝ) - Real.sqrt (detailD (Real.cosh u) (Real.sinh u))) b ∧
      (1 / 101 : ℝ) - Real.sqrt (detailD (Real.cosh u) (Real.sinh u)) < 0 := by
  obtain ⟨r, hrc, hrs, hf, _⟩ := actual_native_stationary_history b u hu
  have hs := Real.sinh_pos_iff.mpr hu
  have hc := Real.cosh_sq_sub_sinh_sq u
  have hco : 1 < Real.cosh u := by
    nlinarith [Real.one_le_cosh u, mul_pos hs hs]
  exact ⟨r, hf, literal_stationary_coframe_derivative b u r (ne_of_gt hb) hu hrc hrs,
    stationary_coframe_covector_nonzero (Real.cosh u) (Real.sinh u) hc hco hs⟩

/-- **GAC2:native-stationary-coframe-source**
(coframe source retained after connection detail stationarity). -/
@[ledger "GAC2:native-stationary-coframe-source"]
theorem coframeLaw : Statement.coframeLaw := by
  exact ⟨stationary_value_coframe_derivative,
    literal_stationary_coframe_derivative,
    connection_stationarity_retains_coframe_source⟩

/-! ## Non-vacuity -/
example : ∃ r : ℝ, nativeSplitFirst 1 (Real.log 2) r 0 = 0 ∧
    HasDerivAt (fun x => literalTwoChildAction x (Real.log 2) r)
      ((1 / 101 : ℝ) - Real.sqrt (detailD (Real.cosh (Real.log 2)) (Real.sinh (Real.log 2)))) 1 ∧
    (1 / 101 : ℝ) - Real.sqrt (detailD (Real.cosh (Real.log 2)) (Real.sinh (Real.log 2))) < 0 :=
  connection_stationarity_retains_coframe_source 1 (Real.log 2) (by norm_num)
    (Real.log_pos (by norm_num))
end

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
