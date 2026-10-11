/-
Part I of "Lean through Artform Calculus": the basics of Lean.
Core Lean 4 only. Every answer Lean gives is pinned with #guard_msgs, so the
file fails if Lean ever answers differently. The printed listings are cut
from this file by ../tools/extract_listings.py:
  /-- info: x -/ #guard_msgs in   (one line)   printed as a comment `-- x`
                                                 after the next line;
  /-- info: ... -/ (several lines)             printed as "Lean replies";
  /-- error: ... -/                            printed as "Lean refuses it".
Check with:  lean LeanBasics.lean
-/

-- ANCHOR: bvalues
/-- info: 5 -/
#guard_msgs in
#eval 2 + 3
/-- info: 2 + 3 : Nat -/
#guard_msgs in
#check 2 + 3
/-- info: "glass bead" -/
#guard_msgs in
#eval "glass " ++ "bead"
/-- info: (2, "two") : Nat × String -/
#guard_msgs in
#check (2, "two")
/-- info: [1, 2, 3] : List Nat -/
#guard_msgs in
#check [1, 2, 3]
/-- info: 3 -/
#guard_msgs in
#eval [1, 2, 3].length
-- ANCHOR_END: bvalues

-- ANCHOR: bnumbers
/-- info: 0 -/
#guard_msgs in
#eval 7 - 10
/-- info: -3 -/
#guard_msgs in
#eval (7 - 10 : Int)
/-- info: 3 -/
#guard_msgs in
#eval 7 / 2
/-- info: 1 -/
#guard_msgs in
#eval 7 % 2
/-- info: (7 : Rat)/12 -/
#guard_msgs in
#eval (1/4 + 1/3 : Rat)
-- ANCHOR_END: bnumbers

-- ANCHOR: bdefs
def double (n : Nat) : Nat := 2 * n

/-- info: 42 -/
#guard_msgs in
#eval double 21
/-- info: 12 -/
#guard_msgs in
#eval double (double 3)
/-- info: double (n : Nat) : Nat -/
#guard_msgs in
#check double
-- ANCHOR_END: bdefs

-- ANCHOR: bfunctions
/-- info: fun n => 2 * n : Nat → Nat -/
#guard_msgs in
#check fun n : Nat => 2 * n

def add (m n : Nat) : Nat := m + n

/-- info: add 2 : Nat → Nat -/
#guard_msgs in
#check add 2

def twice {α : Type} (f : α → α) (x : α) : α := f (f x)

/-- info: 12 -/
#guard_msgs in
#eval twice double 3
-- ANCHOR_END: bfunctions

-- ANCHOR: brecursion
def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

/-- info: 10 -/
#guard_msgs in
#eval sumTo 4
-- ANCHOR_END: brecursion

-- ANCHOR: bmissing
/--
error: Missing cases:
(Nat.succ _)
-/
#guard_msgs in
def isZero : Nat → Bool
  | 0 => true
-- ANCHOR_END: bmissing

-- ANCHOR: binductive
inductive Colour where
  | light
  | dark

inductive Tree where
  | leaf : Char → Tree
  | node : Tree → Tree → Tree
-- ANCHOR_END: binductive

-- ANCHOR: btreesize
def Tree.size : Tree → Nat
  | .leaf _   => 1
  | .node s t => s.size + t.size

def abc : Tree := .node (.leaf 'a') (.node (.leaf 'b') (.leaf 'c'))

/-- info: 3 -/
#guard_msgs in
#eval abc.size
-- ANCHOR_END: btreesize

-- ANCHOR: bstructure
structure Interval where
  lo : Nat
  hi : Nat

def i : Interval := { lo := 2, hi := 5 }
def j : Interval := ⟨2, 5⟩

/-- info: 3 -/
#guard_msgs in
#eval i.hi - i.lo
-- ANCHOR_END: bstructure

-- ANCHOR: bfin
/-- info: 2 -/
#guard_msgs in
#eval (⟨2, by decide⟩ : Fin 5)
/-- info: 2 -/
#guard_msgs in
#eval (7 : Fin 5)
-- ANCHOR_END: bfin

-- ANCHOR: bdependent
def last (n : Nat) : Fin (n + 1) := ⟨n, by omega⟩

/-- info: last (n : Nat) : Fin (n + 1) -/
#guard_msgs in
#check last

def p : (n : Nat) × Fin n := ⟨3, ⟨1, by decide⟩⟩
-- ANCHOR_END: bdependent

-- ANCHOR: bprop
/-- info: 2 + 3 = 5 : Prop -/
#guard_msgs in
#check (2 + 3 = 5 : Prop)

example : 2 + 3 = 5 := rfl
-- ANCHOR_END: bprop

-- ANCHOR: bfalse
/--
error: Tactic `decide` proved that the proposition
  2 + 2 = 5
is false
-/
#guard_msgs in
example : 2 + 2 = 5 := by decide
-- ANCHOR_END: bfalse

-- ANCHOR: bconnectives
example (p : Prop) : p → p := fun h => h
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example : ∃ n : Nat, n * n = 9 := ⟨3, rfl⟩
-- ANCHOR_END: bconnectives

-- ANCHOR: btactics
example (p q : Prop) : p → (p → q) → q := by
  intro hp hpq
  exact hpq hp

example (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega

example : ∀ n : Fin 10, n.val * n.val % 4 ≠ 2 := by decide
-- ANCHOR_END: btactics

-- ANCHOR: bgauss
theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero      => rfl
  | succ n ih => simp only [sumTo]; grind
-- ANCHOR_END: bgauss

-- ANCHOR: binstances
def sum3 {α : Type} [Add α] (a b c : α) : α := a + b + c

/-- info: 6 -/
#guard_msgs in
#eval sum3 1 2 3
/-- info: 1 -/
#guard_msgs in
#eval sum3 (1/2 : Rat) (1/3) (1/6)
-- ANCHOR_END: binstances

-- ANCHOR: bmismatch
/--
error: Type mismatch
  "four"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs in
example : double 2 = "four" := rfl
-- ANCHOR_END: bmismatch

-- ANCHOR: bunknown
/-- error: Unknown identifier `doubel` -/
#guard_msgs in
#eval doubel 21
-- ANCHOR_END: bunknown
