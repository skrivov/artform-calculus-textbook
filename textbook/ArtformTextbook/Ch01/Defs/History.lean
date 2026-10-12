import Mathlib.Algebra.BigOperators.Group.List.Basic
import ArtformTextbook.Ch01.Defs.Time

/-!
# Histories, ticks and cyclarchies (*Time, clocks, and measurement*)

* `LinearTime n`: the line of `n` positions, each followed by the next, the
  last terminal; beside the cycle `CycleTime n`.
* Definition 1.6: a transition graph, the histories `Path_H(G)` of `H`
  transitions whose endpoints fit, and the record
  `OccurrenceHistory(G; γ) : OccurrenceHistoryData(G)`, which keeps the
  positions `I_H = LinearTime(H + 1)` and the transition at each step,
  repeated uses included. The projection `h` reads the state at each position.
* Definition 1.7: a tick realization of a transition graph on a pointed cycle,
  `(ℓ, c) : TickRealization(G, T)`, with its data `ℓ : TickData(G, T)` (a phase
  projection, an initial state and a tick label for each transition) and its
  certificate `c : TickLaw(ℓ)`.
* Definition 1.8: a finite cyclarchy `Cyclarchy(N) : CyclarchyData(N)` on a
  radix list, with its digit states, zero, addition with carry, unit
  increment and checkpoint levels.
-/

namespace Artform

/-- The line `LinearTime(n)` (*Time, clocks, and measurement*): the positions
`0, …, n - 1`, where `t + 1` follows `t`, and the last position is terminal. -/
abbrev LinearTime (n : ℕ) : TimeForm where
  cells := Fin n
  next t := if h : t.val + 1 < n then some ⟨t.val + 1, h⟩ else none
  next_injective s t u hs ht := by
    split_ifs at hs ht
    · have := (Option.some.inj hs).trans (Option.some.inj ht).symm
      exact Fin.ext (by simpa using congrArg Fin.val this)

/-! ## Definition 1.6: occurrence histories -/

/-- **Definition 1.6** (transition graph): the states, the named transitions,
and the source and the target of each transition. -/
@[book "def:time-history"]
structure TransitionGraph where
  /-- The states. -/
  S : Type
  /-- The named transitions. -/
  T : Type
  /-- The source of each transition. -/
  src : T → S
  /-- The target of each transition. -/
  tgt : T → S

/-- **Definition 1.6** (the histories `Path_H(G)`). A finite history
`γ = (x₀, a₀, x₁, …, a_{H-1}, x_H)`: `H` transitions whose endpoints fit,
`a_i : x_i ⟶ x_{i+1}`. -/
@[book "def:time-history"]
structure TransitionGraph.Path (G : TransitionGraph) (H : ℕ) where
  /-- The states `x₀, …, x_H`. -/
  x : Fin (H + 1) → G.S
  /-- The transitions `a₀, …, a_{H-1}`. -/
  a : Fin H → G.T
  /-- Each transition starts where the history is. -/
  src_eq : ∀ i, G.src (a i) = x i.castSucc
  /-- Each transition ends at the next state. -/
  tgt_eq : ∀ i, G.tgt (a i) = x i.succ

/-- **Definition 1.6** (occurrence history data, `OccurrenceHistoryData(G)`):
the record of a finite history. It keeps the number `H` of its transitions,
and the history itself: the state at each of its `H + 1` positions and the
transition at each step, including repeated uses of the same transition. -/
@[book "def:time-history"]
structure OccurrenceHistoryData (G : TransitionGraph) where
  /-- The number of transitions. -/
  H : ℕ
  /-- The history. -/
  path : G.Path H

/-- **Definition 1.6** (occurrence history): `OccurrenceHistory(G; γ)`, the
record of the history `γ : Path_H(G)`. -/
@[book "def:time-history"]
def OccurrenceHistory (G : TransitionGraph) {H : ℕ} (γ : G.Path H) :
    OccurrenceHistoryData G :=
  ⟨H, γ⟩

namespace OccurrenceHistoryData

variable {G : TransitionGraph} (o : OccurrenceHistoryData G)

/-- **Definition 1.6** (occurrence positions): `I_H = LinearTime(H + 1)`. -/
@[book "def:time-history"]
abbrev positions : TimeForm := LinearTime (o.H + 1)

/-- **Definition 1.6** (the projection `h`): the state at each position,
`h(i) = x_i`. It may give the same state at different positions. -/
@[book "def:time-history"]
def h : o.positions.cells → G.S := o.path.x

/-- The transition retained at each step. -/
def transition : Fin o.H → G.T := o.path.a

end OccurrenceHistoryData

/-! ## Definition 1.7: tick realizations -/

/-- A pointed cycle (*Time, clocks, and measurement*): the cycle
`CycleTime(n)`, with the successor `s(t) = t + 1`, and a base phase `t₀`. -/
structure PointedCycle where
  /-- The number of phases. -/
  n : ℕ
  [neZero : NeZero n]
  /-- The base phase `t₀`. -/
  base : Fin n

attribute [instance] PointedCycle.neZero

namespace PointedCycle

/-- The cycle itself, `CycleTime(n)`. -/
abbrev time (T : PointedCycle) : TimeForm := CycleTime T.n

/-- The successor `s` of the cycle. -/
def s (T : PointedCycle) (t : T.time.cells) : T.time.cells := t + 1

end PointedCycle

/-- **Definition 1.7** (tick data, `TickData(G, T)`): a phase projection
`q : S_G → cells(T)`, an initial state `x₀ ∈ S_G`, and a label
`κ(a) ∈ {0, 1}` for each admitted transition `a`, which says whether that
transition registers a tick. -/
@[book "def:time-ticks"]
structure TickData (G : TransitionGraph) (T : PointedCycle) where
  /-- The phase projection `q`. -/
  q : G.S → T.time.cells
  /-- The initial state `x₀`. -/
  x₀ : G.S
  /-- The tick label `κ(a)` of each transition. -/
  κ : G.T → Fin 2

/-- **Definition 1.7** (the tick law, `TickLaw(ℓ)`): what a certificate checks.
For each transition `a : x ⟶ x'`, `q(x') = q(x)` when `κ(a) = 0` and
`q(x') = s(q(x))` when `κ(a) = 1`; and the initial phase is the base phase,
`q(x₀) = t₀`. -/
@[book "def:time-ticks"]
def TickLaw {G : TransitionGraph} {T : PointedCycle} (ℓ : TickData G T) : Prop :=
  (∀ a, ℓ.κ a = 0 → ℓ.q (G.tgt a) = ℓ.q (G.src a)) ∧
  (∀ a, ℓ.κ a = 1 → ℓ.q (G.tgt a) = T.s (ℓ.q (G.src a))) ∧
  ℓ.q ℓ.x₀ = T.base

/-- **Definition 1.7** (tick realization, `(ℓ, c) : TickRealization(G, T)`):
tick data with its certificate. -/
@[book "def:time-ticks"]
structure TickRealization (G : TransitionGraph) (T : PointedCycle) where
  /-- The data `ℓ`. -/
  data : TickData G T
  /-- The certificate `c`. -/
  cert : TickLaw data

/-! ## Definition 1.8: cyclarchies -/

/-- A radix list `N = (N₁, …, N_r)` for a cyclarchy: nonempty, with every
radix at least `2`. The first radix is that of the least significant digit. -/
structure RadixList where
  /-- The radices. -/
  N : List ℕ
  /-- There is at least one digit. -/
  ne_nil : N ≠ []
  /-- Every radix is at least `2`. -/
  two_le : ∀ k ∈ N, 2 ≤ k

namespace RadixList

variable (R : RadixList)

/-- The number `r` of digits. -/
abbrev r : ℕ := R.N.length

/-- The radix of digit `i`; digit `0` is the book's least significant digit
`a₁`. -/
def radix (i : Fin R.r) : ℕ := R.N.get i

theorem two_le_radix (i : Fin R.r) : 2 ≤ R.radix i := R.two_le _ (List.get_mem _ _)

theorem radix_pos (i : Fin R.r) : 0 < R.radix i := by
  have := R.two_le_radix i
  omega

/-- `P_k = N₁ ⋯ N_k`, so `P₀ = 1`. -/
def P (k : ℕ) : ℕ := (R.N.take k).prod

/-- The digit states `S_N = ∏ᵢ {0, …, Nᵢ - 1}`. -/
abbrev Digits : Type := (i : Fin R.r) → Fin (R.radix i)

/-- The zero state `0_N = (0, …, 0)`. -/
def zero : R.Digits := fun i => ⟨0, R.radix_pos i⟩

/-- The value of digit `i` as a number, and `0` beyond the last digit. -/
def digit (a : R.Digits) (i : ℕ) : ℕ := if h : i < R.r then (a ⟨i, h⟩).val else 0

/-- The carries of the sum of `a` and `b`: `c₀ = 0` and
`c_{i+1} = ⌊(aᵢ + bᵢ + cᵢ) / Nᵢ⌋`. -/
def carry (a b : R.Digits) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (R.digit a i + R.digit b i + carry a b i) / R.N.getD i 1

/-- Addition with carry, from the least significant digit:
`(a ⊕ b)ᵢ = (aᵢ + bᵢ + cᵢ) mod Nᵢ`. The final carry is discarded. -/
def add (a b : R.Digits) : R.Digits := fun i =>
  ⟨(R.digit a i + R.digit b i + R.carry a b i) % R.radix i, Nat.mod_lt _ (R.radix_pos i)⟩

/-- The unit `(1, 0, …, 0)`. -/
def unit : R.Digits := fun i =>
  ⟨if i.val = 0 then 1 else 0, by have := R.two_le_radix i; split_ifs <;> omega⟩

/-- The unit increment: add `(1, 0, …, 0)`. -/
def incr (a : R.Digits) : R.Digits := R.add a R.unit

/-- A checkpoint of level `k`: the lowest `k` digits are all zero, as they are
after a multiple of `P_k` increments from zero. -/
def AtCheckpoint (k : ℕ) (a : R.Digits) : Prop := ∀ i : Fin R.r, i.val < k → (a i).val = 0

end RadixList

/-- **Definition 1.8** (cyclarchy data, `CyclarchyData(N)`): what a cyclarchy
retains: its digit states with the zero state, addition with carry, the unit
increment, and the checkpoint levels. -/
@[book "def:time-cyclarchy"]
structure CyclarchyData (R : RadixList) where
  /-- The zero state `0_N`. -/
  zero : R.Digits
  /-- Addition with carry. -/
  add : R.Digits → R.Digits → R.Digits
  /-- The unit increment. -/
  incr : R.Digits → R.Digits
  /-- The checkpoint levels: `checkpoint k a` marks level `k`. -/
  checkpoint : ℕ → R.Digits → Prop

/-- **Definition 1.8** (finite cyclarchy, `Cyclarchy(N) : CyclarchyData(N)`):
the cyclarchy with the radix list `N`. -/
@[book "def:time-cyclarchy"]
def Cyclarchy (R : RadixList) : CyclarchyData R :=
  ⟨R.zero, R.add, R.incr, R.AtCheckpoint⟩

/-! ## Non-vacuity -/

/-- Two decimal digits. -/
abbrev decimal2 : RadixList := ⟨[10, 10], by simp, by simp⟩

/-- Nine, in two decimal digits. -/
def decimalNine : decimal2.Digits := fun i =>
  if h : i.val = 0 then
    ⟨9, by
      have : i = ⟨0, by decide⟩ := Fin.ext h
      subst this
      decide⟩
  else decimal2.zero i

/-- In two decimal digits, nine and one make ten: the carry reaches the second
digit, and the state is a checkpoint of level `1`. -/
example :
    (Cyclarchy decimal2).incr decimalNine ⟨0, by decide⟩ = ⟨0, by decide⟩ ∧
      (Cyclarchy decimal2).incr decimalNine ⟨1, by decide⟩ = ⟨1, by decide⟩ ∧
      (Cyclarchy decimal2).checkpoint 1 ((Cyclarchy decimal2).incr decimalNine) := by
  refine ⟨by decide, by decide, fun i hi => ?_⟩
  have : i = ⟨0, by decide⟩ := Fin.ext (by change i.val = 0; omega)
  subst this
  decide

/-- A transition graph with one state and one transition, a loop. -/
def loopGraph : TransitionGraph := ⟨Unit, Unit, fun _ => (), fun _ => ()⟩

/-- The history that takes the loop twice. -/
def loopTwice : loopGraph.Path 2 := ⟨fun _ => (), fun _ => (), fun _ => rfl, fun _ => rfl⟩

/-- The record keeps both uses of the one transition. -/
example : (OccurrenceHistory loopGraph loopTwice).H = 2 ∧
    (OccurrenceHistory loopGraph loopTwice).transition ⟨0, by decide⟩ =
      (OccurrenceHistory loopGraph loopTwice).transition ⟨1, by decide⟩ :=
  ⟨rfl, rfl⟩

end Artform
