import ArtformTextbook

/-!
# A tour of the repository

The listings of Part III of the guide "Lean through Artform Calculus" that are
not cut from the library itself. Unlike the files of Parts I and II, this one
imports the library, and with it Mathlib. Every answer of Lean that the guide
quotes is pinned here with `#guard_msgs`.
-/

open Artform

/-! ## From core Lean to Mathlib -/

-- ANCHOR: tfintype
/-- info: 5 -/
#guard_msgs in
#eval Fintype.card (Fin 5)
/-- info: 6 -/
#guard_msgs in
#eval Fintype.card (Fin 2 × Fin 3)
/-- info: 5 -/
#guard_msgs in
#eval Fintype.card (OrderedForm.glue (.rod 2) (.rod 3)).cells
example : ∀ i : Fin 10, i.val * i.val % 4 ≠ 2 := by decide
-- ANCHOR_END: tfintype

-- ANCHOR: tsums
/-- info: 10 -/
#guard_msgs in
#eval ∑ k ∈ Finset.range 5, k
example : ∑ k ∈ Finset.range 5, k = 10 := by decide
example (n : ℕ) : 2 * ∑ k ∈ Finset.range (n + 1), k = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
-- ANCHOR_END: tsums

-- ANCHOR: tzmod
/-- info: 1 -/
#guard_msgs in
#eval (5 : ZMod 8) + 4
/-- info: 6 -/
#guard_msgs in
#eval (3 : ZMod 8) - 5
example : ∀ a : ZMod 8, a + a + a + a + a + a + a + a = 0 := by decide
example : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
-- ANCHOR_END: tzmod

-- ANCHOR: tperm
/-- info: 0 -/
#guard_msgs in
#eval finRotate 4 3
example : finRotate 4 ^ 4 = 1 := by decide
example : finRotate 4 ^ 2 ≠ 1 := by decide
example (f g : Equiv.Perm (Fin 4)) (x : Fin 4) : (f * g) x = f (g x) := rfl
-- ANCHOR_END: tperm

-- ANCHOR: ttally
/-- info: ![1, 1, 2, 0] -/
#guard_msgs in
#eval squareLaw.tick ![1, 2, 0, 1]
/-- info: 1 -/
#guard_msgs in
#eval squareTotal ![1, 2, 0, 1]
example (p q : Fin 4 → ZMod 3) :
    squareTotal (p + q) = squareTotal p + squareTotal q :=
  map_add squareTotal p q
-- ANCHOR_END: ttally

-- ANCHOR: texact
/--
info: Try this:
  [apply] exact Nat.add_comm a b
-/
#guard_msgs in
example (a b : ℕ) : a + b = b + a := by exact?
-- ANCHOR_END: texact

/-! ## How the book is written in Lean -/

-- ANCHOR: tbook
/--
info: Artform.Statement.noether : Prop
---
info: Artform.noether : Statement.noether
-/
#guard_msgs in
#book "thm:noether"
-- ANCHOR_END: tbook

/-! ## How the repository checks itself -/

-- ANCHOR: taxioms
/--
info: 'Artform.noether' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noether
-- ANCHOR_END: taxioms
