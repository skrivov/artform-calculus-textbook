import ArtformScores.GravityBridge.Native.Full40.ShiftsStatements

/-! # Independent shifts and the periodic incoming transpose -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {X K : Type*} [AddCommGroup X] [CommRing K]

omit [CommRing K] in
lemma shift_compose (a b : X) (f : X → K) : shift a (shift b f) = shift (a + b) f := by
  funext x
  simp [shift, add_assoc]
omit [CommRing K] in
lemma shift_commute (a b : X) (f : X → K) : shift a (shift b f) = shift b (shift a f) := by
  rw [shift_compose, shift_compose, add_comm a b]
omit [CommRing K] in
lemma shift_inverse (a : X) (f : X → K) : shift (-a) (shift a f) = f := by
  rw [shift_compose]
  funext x
  simp [shift]
lemma difference_commute (a b : X) (f : X → K) :
    difference a (difference b f) = difference b (difference a f) := by
  funext x
  simp [difference, shift, add_assoc, add_comm a b]
  ring
lemma shift_adjoint [Fintype X] (a : X) (f g : X → K) :
    ∑ x, shift a f x * g x = ∑ x, f x * shift (-a) g x := by
  classical
  apply Fintype.sum_equiv (Equiv.addRight a)
  intro x
  simp [shift]
lemma difference_adjoint [Fintype X] (a : X) (f g : X → K) :
    ∑ x, difference a f x * g x = ∑ x, f x * difference (-a) g x := by
  simp only [difference, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [shift_adjoint]

lemma independent_grid_shifts : ∀ i j : Fin 4, i ≠ j →
    shift (gridUnit i) gridPulse (-gridUnit i) = 1 ∧
    shift (gridUnit j) gridPulse (-gridUnit i) = 0 := by decide +kernel

/-- **GAC2:native-shift-adjoint**
(independent shifts and the periodic incoming transpose). -/
@[ledger "GAC2:native-shift-adjoint"]
theorem shiftsLaw : Statement.shiftsLaw := by
  intro X K _ _
  exact ⟨shift_compose,
    shift_commute,
    shift_inverse,
    difference_commute,
    shift_adjoint,
    difference_adjoint,
    independent_grid_shifts⟩

/-! ## Non-vacuity -/
example : shift (gridUnit 0) gridPulse (-gridUnit 0) = 1 ∧
    shift (gridUnit 1) gridPulse (-gridUnit 0) = 0 :=
  independent_grid_shifts 0 1 (by decide)

end Artform.Scores.GravityBridge.Native.Full40
