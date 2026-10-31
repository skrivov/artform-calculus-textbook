import ArtformScores.NonabelianGravity.Dynamics

/-! # NGB: noncommuting examples and failed orientation/schedule shortcuts -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
abbrev S3 := ClassicalNonabelian.S3
def r : S3 := ClassicalNonabelian.rotation
def t : S3 := ClassicalNonabelian.reflection
def witness : State S3 := ⟨![t,t,t,1,1,1,r],![t,t,t,t,1,1,1]⟩
lemma witness_gauss : Gauss witness := by unfold Gauss; decide +kernel
lemma witness_noncommuting : holonomy witness.U 1 3*outgoing witness 1 ≠
    outgoing witness 1*holonomy witness.U 1 3 := by decide +kernel
lemma witness_initial_order : holonomy witness.U 0 0*holonomy witness.U 0 0=1 := by
  decide +kernel
lemma witness_final_order : holonomy (tick witness).U 0 0*holonomy (tick witness).U 0 0 ≠ 1 := by
  decide +kernel
lemma witness_orbit_changes : ¬ ∃ h, gauge h witness=tick witness := by
  rintro ⟨h,hh⟩
  have hc := holonomy_gauge h witness 0 0
  rw [hh] at hc
  have he : holonomy (tick witness).U 0 0*holonomy (tick witness).U 0 0=
      h 1*(holonomy witness.U 0 0*holonomy witness.U 0 0)*(h 1)⁻¹ := by
    simp only [stepTarget] at hc
    norm_num at hc
    rw [hc]
    group
  rw [witness_initial_order] at he
  exact witness_final_order (by simpa using he)

def partialKick {G : Type} [Group G] (s : State G) : State G :=
  ⟨s.U,Function.update s.P 0 (holonomy s.U 0 0*s.P 0)⟩
lemma partial_breaks_gauss : ¬ Gauss (partialKick witness) := by unfold Gauss; decide +kernel
def wrongOrientation {G : Type} [Group G] (s : State G) : State G :=
  ⟨s.U,Function.update (kick 1 false s).P 1 (holonomy s.U 1 2*s.P 1)⟩
lemma wrong_orientation_breaks : ¬ Gauss (wrongOrientation witness) := by
  unfold Gauss
  decide +kernel
def wrongDefect {G : Type} [Group G] (s : State G) : G :=
  outgoing s 1*outgoing s 4*s.P 0
lemma wrong_order_initial : wrongDefect witness=1 := by decide +kernel
lemma wrong_order_after : wrongDefect (kick 1 false witness) ≠ 1 := by decide +kernel
lemma drift_interposition_changes :
    kick 1 false (drift false (kick 0 false witness)) ≠
      drift false (kick 1 false (kick 0 false witness)) := by
  intro hh
  have he := congrArg (fun s : State S3 => s.U 1) hh
  exact (by decide +kernel :
    (kick 1 false (drift false (kick 0 false witness))).U 1 ≠
    (drift false (kick 1 false (kick 0 false witness))).U 1) he

/-! ## Non-vacuity -/
example : Gauss witness ∧ Gauss (tick witness) ∧
    ¬ ∃ h, gauge h witness=tick witness :=
  ⟨witness_gauss,(run_gauss _ _).mpr witness_gauss,witness_orbit_changes⟩
end Artform.Scores.NonabelianGravity
