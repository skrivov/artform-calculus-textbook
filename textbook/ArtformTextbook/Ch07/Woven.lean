import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import ArtformTextbook.Ch05.Patterns
import ArtformTextbook.Ch07.Statements.Woven

/-!
# A kept count is woven: coherent laws (Section 7.4)

The proof of Corollary 7.3. The book's proof reads the weights `|U[x', x]|²` from each basis
label as a stochastic realizer on the labels, with the same halos and the same count, notes
that emptying cells of a label gives a label, and applies Theorem 5.45. Here the core of
Theorem 5.45, `Patterns.weave_of_steps`, is applied directly to the steps `x → x'` with
`U[x', x] ≠ 0`: every label is legal, so emptying cells keeps labels legal; and a table that
some step from `x` shows on `V` has positive weight in the report of `V` from `x`, so by
no-signalling it has positive weight from every label that agrees with `x` on `H(V)`, and some
step from that label shows it.
-/

namespace Artform

open Finset

/-- **Corollary 7.3** (a kept count is woven: coherent laws). Let a script keep a count: every
step `x → x'` with `U[x', x] ≠ 0` keeps it. Then each such step has a weave along every
no-signalling halo of the script. -/
@[book "cor:qr-woven"]
theorem qrWoven : Statement.qrWoven := by
  intro Cell _ U c hK H hNS x x' hxx'
  classical
  refine Patterns.weave_of_steps (Legal := fun _ => True)
    (Step := fun x x' => U.coeff x' x ≠ 0) (fun _ _ _ => trivial)
    (fun V x z x' _ _ hag hst => ?_) (fun x x' _ h => hK x x' h) trivial hxx'
  -- The table that `x'` shows on `V` has positive weight from `x`, and so from `z`.
  have hpos : 0 < U.showWeight x V (restrictTo V x') := by
    refine sum_pos' (fun z _ => ?_) ⟨x', mem_univ _, ?_⟩
    · split_ifs
      · exact Complex.normSq_nonneg _
      · exact le_rfl
    · rw [ite_eq_left rfl]
      exact Complex.normSq_pos.2 hst
  rw [hNS V x z hag] at hpos
  -- Some label `z'` that shows it there has `U[z', z] ≠ 0`.
  by_contra hno
  push Not at hno
  refine absurd hpos (not_lt.2 (sum_nonpos fun z' _ => ?_))
  split_ifs with he
  · have h0 : U.coeff z' z = 0 := by
      by_contra hne
      obtain ⟨p, hp, hne'⟩ := hno z' hne
      exact hne' (congrFun he ⟨p, hp⟩)
    rw [h0, map_zero]
  · exact le_rfl

/-! ## Non-vacuity -/

namespace SwapWeaveExample

/-- The two cells `s` (`0`) and `r` (`1`). -/
abbrev Cell : Type := Fin 2

/-- The other cell. -/
def other (c : Cell) : Cell := 1 - c

/-- The label after the swap: `s` and `r` exchange their values. -/
def swap (x : BasisLabel Cell) : BasisLabel Cell := fun c => x (other c)

open Classical in
/-- The table of the swap `CX_{s→r}, CX_{r→s}, CX_{s→r}`: coefficient `1` from each label to
the label with the values of `s` and `r` exchanged, and `0` elsewhere. -/
noncomputable def script : ScriptTable Cell := ⟨fun y x => if y = swap x then 1 else 0⟩

/-- The count of the cells that hold `1`, one token each. -/
def count : Count (binaryCells Cell) := ⟨fun _ a => a.val, fun _ => rfl⟩

/-- The halo of the swap: `H(s) = {r}` and `H(r) = {s}`. -/
def halo (c : Cell) : Set Cell := {other c}

open Classical in
theorem showWeight_eq (x : BasisLabel Cell) (V : Set Cell) (τ : (p : V) → Fin 2) :
    script.showWeight x V τ = if restrictTo V (swap x) = τ then 1 else 0 := by
  unfold ScriptTable.showWeight
  rw [Finset.sum_eq_single (swap x)]
  · simp [script]
  · intro z _ hz
    simp [script, hz]
  · intro h
    simp at h

theorem keeps : ∀ x x' : BasisLabel Cell, script.coeff x' x ≠ 0 → count.N x' = count.N x := by
  intro x x' h
  have hx' : x' = swap x := by
    by_contra hne
    exact h (by simp [script, hne])
  subst hx'
  simp only [Count.N, count, swap, other, Fin.sum_univ_two]
  rw [add_comm]
  rfl

theorem noSignalling : script.NoSignalling halo := by
  intro V x z hag
  have hr : restrictTo V (swap x) = restrictTo V (swap z) := by
    funext ⟨p, hp⟩
    exact hag (other p) (Set.mem_biUnion hp rfl)
  funext τ
  rw [showWeight_eq, showWeight_eq, hr]

end SwapWeaveExample

open SwapWeaveExample in
/-- Corollary 7.3 on the swap `CX_{s→r}, CX_{r→s}, CX_{s→r}` of Section 7.4: it keeps the count
of the cells that hold `1`, and `H(s) = {r}`, `H(r) = {s}` is a no-signalling halo of it. So its
step from `10` to `01` has a weave, which moves the token from `s` to `r`, along the halo of
`r`. -/
example : (∀ x x' : BasisLabel Cell, script.coeff x' x ≠ 0 → count.N x' = count.N x) ∧
    script.NoSignalling halo ∧ Nonempty (Weave halo count ![1, 0] ![0, 1]) := by
  refine ⟨keeps, noSignalling, qrWoven Cell script count keeps halo noSignalling _ _ ?_⟩
  have h : (![0, 1] : BasisLabel Cell) = swap ![1, 0] := by decide
  simp [script, h]

end Artform
