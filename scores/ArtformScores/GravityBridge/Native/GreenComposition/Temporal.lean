import ArtformScores.GravityBridge.Native.GreenComposition.TemporalStatements

/-! # Finite-range temporal cut with its original incoming terms -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {K : Type*} [CommRing K]

open scoped BigOperators
lemma backward_edge_telescoping (f : ℤ → K) (n : ℤ) (r : ℕ) :
    (∑ j ∈ Finset.range r, (f (n - (j : ℤ)) - f (n - 1 - (j : ℤ)))) = f n - f (n - (r : ℤ)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have he : n - 1 - (r : ℤ) = n - ((r + 1 : ℕ) : ℤ) := by push_cast;ring
    rw [he]
    abel

lemma complete_temporal_cut_difference (edge : ℤ → ℕ → K) (R : ℕ) (n : ℤ) :
    cutSum edge R n - cutSum edge R (n - 1) = rowSkew edge R n := by
  unfold cutSum rowSkew
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_sub_distrib]
  exact backward_edge_telescoping (fun m => edge m r) n r

lemma sourced_cut_difference (edge : ℤ → ℕ → K) (R : ℕ) (n : ℤ) (h f g : K)
    (hrow : rowSkew edge R n = g - f) :
    h * cutSum edge R n - h * cutSum edge R (n - 1) = h * (g - f) := by
  rw [← mul_sub, complete_temporal_cut_difference, hrow]

lemma original_incoming_temporal_identity {V : Type*} (B : ℕ → V → V → K)
    (x y : ℤ → V) (R : ℕ) (n : ℤ) :
    cutSum (operatorEdge B x y) R n - cutSum (operatorEdge B x y) R (n - 1) =
      pairedIncomingStencil B x y R n - pairedIncomingStencil B y x R n := by
  rw [complete_temporal_cut_difference]
  unfold rowSkew pairedIncomingStencil
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [operatorEdge, sub_add_cancel]
  ring

lemma source_contact_cannot_be_erased :
    cutSum (fun n r => if r = 1 then (n : ℚ) else 0) 1 1-
      cutSum (fun n r => if r = 1 then (n : ℚ) else 0) 1 0 = 1 := by
  norm_num [cutSum]

/-- **GAC2:complete-temporal-cut-stencil**
(finite-range temporal cut with its original incoming terms). -/
@[ledger "GAC2:complete-temporal-cut-stencil"]
theorem temporalLaw : Statement.temporalLaw := by
  intro K _
  exact ⟨backward_edge_telescoping,
    complete_temporal_cut_difference,
    sourced_cut_difference,
    original_incoming_temporal_identity,
    source_contact_cannot_be_erased⟩

/-! ## Non-vacuity -/
example : cutSum (fun n r => if r = 1 then (n : ℚ) else 0) 1 1-
    cutSum (fun n r => if r = 1 then (n : ℚ) else 0) 1 0 = 1 :=
  source_contact_cannot_be_erased

end Artform.Scores.GravityBridge.Native.GreenComposition
