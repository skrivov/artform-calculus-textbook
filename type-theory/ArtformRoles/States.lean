import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# States counted by their tables

Sections 2.2 and 12.5 of the paper. A state of a frame is a table with
evidence that it is legal: in the calculus `State(A)` is the witness sum
`Σ(t :_W Table(A)). Legal_A(t)`. The sum has one element for each legality
proof of a table, while the book counts a legal table once. The calculus has
no proof-irrelevance rule, so the book's count is an observation of states
through their tables (Astra's finding 2, review of 2026-10-12;
`Calculus.Book.Chess.two_legal_states` gives two distinct normal states with
one table).

* `tables_of_states`: observed through its table, a state is a legal table:
  the tables of the states are exactly the legal tables.
* `card_states_eq_iff`: the sum has as many elements as there are legal
  tables exactly when no table has two legality proofs.
-/

namespace Artform.Roles

open Finset

variable {T : Type*} (Legal : T → Type*)

/-- The tables of the states are the legal tables. -/
theorem tables_of_states :
    Set.range (Sigma.fst : (Σ t, Legal t) → T) = {t | Nonempty (Legal t)} := by
  ext t
  constructor
  · rintro ⟨⟨t', ℓ⟩, rfl⟩
    exact ⟨ℓ⟩
  · rintro ⟨ℓ⟩
    exact ⟨⟨t, ℓ⟩, rfl⟩

/-- Counting states as pairs counts legality proofs: the sum has as many
elements as there are legal tables exactly when every table has at most one
legality proof. -/
theorem card_states_eq_iff [Fintype T] [∀ t, Fintype (Legal t)]
    [DecidablePred fun t => Nonempty (Legal t)] :
    Fintype.card (Σ t, Legal t) = Fintype.card {t // Nonempty (Legal t)} ↔
      ∀ t, Fintype.card (Legal t) ≤ 1 := by
  rw [Fintype.card_sigma, Fintype.card_subtype, Finset.card_filter]
  have hle : ∀ t ∈ (univ : Finset T),
      (if Nonempty (Legal t) then 1 else 0) ≤ Fintype.card (Legal t) := by
    intro t _
    split_ifs with h
    · exact Fintype.card_pos_iff.mpr h
    · exact Nat.zero_le _
  rw [eq_comm, Finset.sum_eq_sum_iff_of_le hle]
  constructor
  · intro h t
    have := h t (mem_univ t)
    split_ifs at this <;> omega
  · intro h t _
    have := h t
    split_ifs with hne
    · have := Fintype.card_pos_iff.mpr hne
      omega
    · exact (Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hne)).symm

/-! ## Non-vacuity -/

/-- One table with two legality proofs: two states, one legal table. -/
example : Fintype.card (Σ _ : Unit, Fin 2) = 2 := by decide

example : ¬∀ _ : Unit, Fintype.card (Fin 2) ≤ 1 := by decide

end Artform.Roles
