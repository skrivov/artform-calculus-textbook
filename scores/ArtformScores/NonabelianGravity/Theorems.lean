import ArtformScores.NonabelianGravity.Statements

/-! # NGB: checked submissions, pending independent fidelity review -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity

/-- **NGB:two-face-geometry** (actual signed incidence and gauge-stable Gauss). -/
@[ledger "NGB:two-face-geometry"]
theorem twoFaceGeometry : Statement.twoFaceGeometry := by
  exact ⟨rfl,rfl,rfl,rfl,star_complete,star_nodup,fun _ _ s h =>
    ⟨defect_star s,defect_gauge h s,gauss_gauge h s,holonomy_gauge h s⟩⟩

/-- **NGB:oriented-score** (all-raw defects, prefix laws and reduced inverses). -/
@[ledger "NGB:oriented-score"]
theorem orientedScore : Statement.orientedScore := by
  intro G _ w s h
  exact ⟨run_inverse w s,run_inverse_other w s,fun n => run_defect (w.take n) s,
    run_gauge w h s,fun f b => ⟨kick_defect f b s,kick_inverse f b s⟩,
    fun b => ⟨drift_defect b s,drift_inverse b s⟩,
    fun b => reversed_shared b s,fun b c => kicks_commute b c s,
    admitted_inverse w,fun x => ⟨physical_inverse w x,physical_inverse_other w x⟩⟩

/-- **NGB:legal-overlap** (complete face commits in a three-phase Gauss law). -/
@[ledger "NGB:legal-overlap"]
theorem legalOverlap : Statement.legalOverlap := by
  intro G _
  exact ⟨fun g x => ⟨trivial,rfl,rfl,profile_apply g x⟩,profile_covariant,
    faces_not_compatible,rfl,fun _ h => h,law_legal,fun _ _ => rfl,
    realizer_wellPosed,realizer_tick⟩

/-- **NGB:noncommuting-controls** (motion beyond gauge and adverse local changes). -/
@[ledger "NGB:noncommuting-controls"]
theorem noncommutingControls : Statement.noncommutingControls := by
  exact ⟨witness_gauss,(run_gauss _ _).mpr witness_gauss,witness_noncommuting,
    witness_initial_order,witness_final_order,witness_orbit_changes,partial_breaks_gauss,
    wrong_orientation_breaks,wrong_order_initial,wrong_order_after,drift_interposition_changes⟩

/-- **NGB:double-dictionary** (source/target conventions and the exact twist word). -/
@[ledger "NGB:double-dictionary"]
theorem doubleDictionary : Statement.doubleDictionary := by
  intro G _ U P ht hs a b
  exact ⟨double_endpoints U P,double_covariance U P ht hs,double_inverse a b,double_drift U P⟩

/-- **NGB:formal-two-form** (finite formal pullbacks and a nonzero coefficient). -/
@[ledger "NGB:formal-two-form"]
theorem formalTwoForm : Statement.formalTwoForm := by
  exact ⟨Maurer.face0_normal,Maurer.face1_normal,Maurer.drift_normal,Maurer.baseline_value,
    fun _ _ pair => Maurer.universal_formal_pullbacks pair⟩

/-- **NGB:word-binding** (the formal word updates cover the actual group maps). -/
@[ledger "NGB:word-binding"]
theorem wordBinding : Statement.wordBinding := by
  intro G _ g
  exact ⟨Maurer.eval_wm g,Maurer.eval_wi g,Maurer.eval_wordKick g,
    Maurer.eval_wordDrift g,Maurer.eval_original⟩

/-- **NGB:neighbor-scaling** (oriented cancellation, jets and the explicit norm defect). -/
@[ledger "NGB:neighbor-scaling"]
theorem neighborScaling : Statement.neighborScaling := by
  refine ⟨fun _ _ s => shared_pair s,?_,?_⟩
  · intro R _ E J F KL KR A B C
    exact ⟨Scaling.common_leading_cancels E J F KL KR,Scaling.drift_scale E J A B C⟩
  · intro R _ L K P hK hP
    refine ⟨Scaling.shared_error L K P hK hP,?_⟩
    intro h CF CK CP hh hCK hCP hf hk hp
    exact ⟨Scaling.shared_budget L K P hK hP h CF CK CP (le_of_lt hh) hCK hCP hf hk hp,
      Scaling.rescaled_budget L K P hK hP h CF CK CP hh hCK hCP hf hk hp⟩

/-! ## Non-vacuity -/
example : Gauss witness ∧ Gauss (tick witness) :=
  ⟨witness_gauss,(run_gauss _ _).mpr witness_gauss⟩
example : ¬ ∃ h, gauge h witness=tick witness := witness_orbit_changes
example : (realizer S3).WellPosed := realizer_wellPosed
example : doubleTarget (doubleA (r:S3) t) (doubleB r t)=t := (double_endpoints r t).1
example : Maurer.value Maurer.witnessPair (Maurer.twiceOmega Maurer.original)=1 :=
  Maurer.baseline_value
example : Maurer.evalState (Maurer.assignment witness) Maurer.original=witness :=
  Maurer.eval_original witness
example : Scaling.times (Scaling.times (Scaling.field (2:ℚ) 3) (Scaling.field 5 7))
    (Scaling.inverseField 2 11)=Scaling.field 5 (-1) := by decide +kernel
end Artform.Scores.NonabelianGravity
