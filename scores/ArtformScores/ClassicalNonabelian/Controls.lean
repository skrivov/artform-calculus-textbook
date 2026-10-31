import ArtformScores.ClassicalNonabelian.Dynamics

/-! # Noncommuting classical controls and the orientation boundary -/
set_option autoImplicit false
namespace Artform.Scores.ClassicalNonabelian
abbrev S3 := Equiv.Perm (Fin 3)
def rotation : S3 := Equiv.swap 0 1*Equiv.swap 1 2
def reflection : S3 := Equiv.swap 0 1

def witness : State S3 :=
  ⟨![1,1,1,rotation,1],![reflection,reflection,1,1,reflection⁻¹]⟩
lemma witness_gauss : Gauss witness := by unfold Gauss; decide +kernel
lemma witness_noncommuting : holonomy witness.U 0*witness.P 0 ≠
    witness.P 0*holonomy witness.U 0 := by decide +kernel
lemma witness_nonflat : holonomy witness.U 3 ≠ 1 := by decide +kernel
lemma witness_flat_after : holonomy (tick witness).U 3=1 := by decide +kernel
lemma witness_kick_changes : kick false witness ≠ witness := by
  intro h
  have hh := congrArg (fun s : State S3 => s.P 0) h
  exact (by decide +kernel : (kick false witness).P 0 ≠ witness.P 0) hh
lemma witness_tick_gauss : Gauss (tick witness) := (run_gauss _ _).mpr witness_gauss
lemma witness_orbit_changes : ¬ ∃ h, gauge h witness=tick witness := by
  rintro ⟨h,hh⟩
  have hc := holonomy_gauge h witness 3
  rw [hh,witness_flat_after] at hc
  have hi := congrArg (fun z => (h 0)⁻¹*z*h 0) hc
  have he : 1=holonomy witness.U 3 := by simpa [canvas,mul_assoc] using hi
  exact witness_nonflat he.symm


def partialKick {G : Type} [Group G] (s : State G) : State G :=
  ⟨s.U,Function.update s.P 0 (holonomy s.U 0*s.P 0)⟩
lemma partial_breaks_gauss : ¬ Gauss (partialKick witness) := by unfold Gauss; decide +kernel

/-- A different local star order is a different Gauss predicate. -/
def wrongDefect {G : Type} [Group G] (s : State G) : canvas.V → G :=
  Function.update (defect s) 2 (outgoing s 2*s.P 4*s.P 1)
lemma wrong_order_initial : wrongDefect witness=1 := by decide +kernel
lemma wrong_order_after : wrongDefect (kick false witness) ≠ 1 := by decide +kernel

abbrev A5 := alternatingGroup (Fin 5)
def rotation5 : A5 := ⟨Equiv.swap 0 1*Equiv.swap 1 2,by
  change Equiv.Perm.sign (Equiv.swap 0 1*Equiv.swap 1 2 : Equiv.Perm (Fin 5))=1
  decide +kernel⟩
def reflection5 : A5 := ⟨Equiv.swap 0 1*Equiv.swap 3 4,by
  change Equiv.Perm.sign (Equiv.swap 0 1*Equiv.swap 3 4 : Equiv.Perm (Fin 5))=1
  decide +kernel⟩
def witness5 : State A5 :=
  ⟨![1,1,1,rotation5,1],![reflection5,reflection5,1,1,reflection5⁻¹]⟩
lemma witness5_gauss : Gauss witness5 := by unfold Gauss; decide +kernel
lemma witness5_noncommuting : holonomy witness5.U 0*witness5.P 0 ≠
    witness5.P 0*holonomy witness5.U 0 := by decide +kernel
lemma witness5_nonflat : holonomy witness5.U 3 ≠ 1 := by decide +kernel
lemma witness5_flat_after : holonomy (tick witness5).U 3=1 := by decide +kernel

variable {G : Type} [Group G]
/-- Reversing an edge interchanges the side on which the kick must act. -/
lemma reversed_kick (U P Q k : G) :
    U⁻¹*Q⁻¹*U=k*(U⁻¹*P⁻¹*U) ↔ Q=P*U*k⁻¹*U⁻¹ := by
  constructor
  · intro h
    have hc := congrArg (fun z => U*z*U⁻¹) h
    have hi := congrArg Inv.inv hc
    simpa only [mul_inv_rev,inv_inv,mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,
      mul_one,one_mul] using hi
  · intro h
    subst Q
    group
lemma uniform_left_for_right (a : G) :
    (∃ k, ∀ p : G, k*p=p*a) ↔ ∀ p : G, a*p=p*a := by
  constructor
  · rintro ⟨k,h⟩
    have hk : k=a := by simpa using h 1
    subst k
    exact h
  · intro h
    exact ⟨a,h⟩
lemma noncentral_orientation_control : ¬ ∃ k : S3, ∀ p : S3, k*p=p*rotation := by
  rw [uniform_left_for_right]
  intro h
  have hh := h reflection
  exact (by decide +kernel : rotation*reflection ≠ reflection*rotation) hh

/-! ## Non-vacuity -/
example : Gauss witness ∧ holonomy witness.U 3 ≠ 1 ∧ holonomy (tick witness).U 3=1 :=
  ⟨witness_gauss,witness_nonflat,witness_flat_after⟩
example : ¬ Gauss (partialKick witness) := partial_breaks_gauss
example : wrongDefect witness=1 ∧ wrongDefect (kick false witness) ≠ 1 :=
  ⟨wrong_order_initial,wrong_order_after⟩
end Artform.Scores.ClassicalNonabelian
