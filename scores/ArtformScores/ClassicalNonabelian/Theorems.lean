import ArtformScores.ClassicalNonabelian.Statements

/-! # Kernel-checked submissions awaiting independent fidelity review -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.ClassicalNonabelian
open Artform

/-- **CNI:geometry-gauss** (ordered local constraint and based holonomy). -/
@[ledger "CNI:geometry-gauss"]
theorem geometryGauss : Statement.geometryGauss := by
  exact ⟨rfl,rfl,rfl,star_complete,star_nodup,fun _ _ s h =>
    ⟨defect_star s,defect_gauge h s,gauss_gauge h s,cyclic_gauss,
      fun e => congrFun (holonomy_word s.U) e,holonomy_transport s.U,holonomy_gauge h s⟩⟩

/-- **CNI:two-shear-score** (full raw and constrained orbit reversibility). -/
@[ledger "CNI:two-shear-score"]
theorem twoShearScore : Statement.twoShearScore := by
  intro G _ w s h
  exact ⟨run_inverse w s,run_inverse_other w s,fun n => run_defect (w.take n) s,run_gauge w h s,
    fun b => ⟨kick_defect b s,drift_defect b s,kick_inverse b s,drift_inverse b s,
      by simp [kick,multiplier_spectator]⟩,
    fun b e => ⟨driftOne_defect b e s,driftOne_inverse b e s⟩,tick_formula s,
    fun x => ⟨admitted_inverse w x,admitted_inverse_other w x⟩,
    fun x => ⟨physical_inverse w x,physical_inverse_other w x⟩⟩

/-- **CNI:legal-native** (owned complete kick and a genuine five-event drift batch). -/
@[ledger "CNI:legal-native"]
theorem legalNative : Statement.legalNative := by
  intro G _
  exact ⟨fun g x => ⟨trivial,rfl,rfl,profile_apply g x⟩,profile_covariant,link_compatible,
    fun x => ⟨rfl,rfl,kickBatch_apply x,driftBatch_apply x⟩,
    rfl,fun _ h => h,law_legal,realizer_wellPosed,batch_order_free,realizer_tick⟩

/-- **CNI:noncommuting-control** (curvature-to-flat physical motion and adverse checks). -/
@[ledger "CNI:noncommuting-control"]
theorem noncommutingControl : Statement.noncommutingControl := by
  exact ⟨witness_gauss,witness_noncommuting,witness_nonflat,witness_flat_after,witness_tick_gauss,
    witness_orbit_changes,witness_kick_changes,partial_breaks_gauss,
    wrong_order_initial,wrong_order_after,fun _ _ => reversed_kick,
    fun _ _ => uniform_left_for_right,
    noncentral_orientation_control,witness5_gauss,witness5_noncommuting,
    witness5_nonflat,witness5_flat_after⟩

/-! ## Non-vacuity -/
example : Gauss witness ∧ holonomy witness.U 3 ≠ 1 ∧ holonomy (tick witness).U 3=1 :=
  ⟨witness_gauss,witness_nonflat,witness_flat_after⟩
example : holonomy witness.U 0*witness.P 0 ≠ witness.P 0*holonomy witness.U 0 :=
  witness_noncommuting
example : defect (tick witness)=defect witness := run_defect _ _
example : ¬ ∃ h, gauge h witness=tick witness := witness_orbit_changes
example : (driftBatch (encode witness)).apps.length=5 ∧
    (kickBatch (encode witness)).apps.length=1 := ⟨rfl,rfl⟩
example : (realizer S3).WellPosed := realizer_wellPosed
example : ¬ Gauss (partialKick witness) := partial_breaks_gauss
example : wrongDefect witness=1 ∧ wrongDefect (kick false witness) ≠ 1 :=
  ⟨wrong_order_initial,wrong_order_after⟩
example : Gauss witness5 ∧ holonomy witness5.U 3 ≠ 1 ∧ holonomy (tick witness5).U 3=1 :=
  ⟨witness5_gauss,witness5_nonflat,witness5_flat_after⟩
end Artform.Scores.ClassicalNonabelian
