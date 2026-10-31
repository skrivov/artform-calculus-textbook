import ArtformScores.GravityBridge.Native.NativeCurrent.OwnedWindowStatements

/-! # Owned spatial windows retain their incoming boundary -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent

open scoped BigOperators

variable {X K : Type*} [Fintype X] [AddCommGroup X] [Field K]

open scoped BigOperators
lemma owned_forward_incoming_defect (owner f g : X → K) (s : X) :
    ownedPairing owner f (fun x => g (x + s))-
      ownedPairing owner (fun x => f (x - s)) g = ownedBoundary owner f g s := by
  have he : (∑ x, owner x * f (x - s) * g x) = ∑ x, owner (x + s) * f x * g (x + s) := by
    have ht := Equiv.sum_comp (Equiv.addRight s) (fun x => owner x * f (x - s) * g x)
    change (∑ x, owner (x + s) * f ((x + s) - s) * g (x + s)) = ∑ x, owner x * f (x - s) * g x at ht
    simpa only [add_sub_cancel_right] using ht.symm
  unfold ownedPairing ownedBoundary
  rw [he, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma full_space_no_window_defect (f g : X → K) (s : X) :
    ownedPairing (fun _ => 1) f (fun x => g (x + s)) =
      ownedPairing (fun _ => 1) (fun x => f (x - s)) g := by
  apply sub_eq_zero.mp
  rw [owned_forward_incoming_defect]
  simp [ownedBoundary]

lemma owned_corner_is_nonzero : ownedBoundary window5 leftEdge5 rightEdge5 1 = 1 := by
  decide +kernel

/-- **GAC2:owned-window-incoming-boundary**
(owned spatial windows retain their incoming boundary). -/
@[ledger "GAC2:owned-window-incoming-boundary"]
theorem ownedWindowLaw : Statement.ownedWindowLaw := by
  intro X K _ _ _
  exact ⟨owned_forward_incoming_defect,
    full_space_no_window_defect,
    owned_corner_is_nonzero⟩

/-! ## Non-vacuity -/

example : ownedPairing window5 leftEdge5 (fun x => rightEdge5 (x + 1))-
    ownedPairing window5 (fun x => leftEdge5 (x - 1)) rightEdge5 = 1 := by
  rw [owned_forward_incoming_defect]
  exact owned_corner_is_nonzero

end Artform.Scores.GravityBridge.Native.NativeCurrent
