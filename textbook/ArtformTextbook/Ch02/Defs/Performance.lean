import Mathlib.Order.Hom.Basic
import ArtformTextbook.Ch01.Defs.History

/-!
# Contracts, symmetries, slots and traces (*A dancer's rules*; *The music*; *Trajectory and trace*)

* Definition 2.3: a contract for a stretch of a performance between two
  checkpoints, and the composition of two contracts.
* Definition 2.4: a symmetry of a dance, a script on its states that keeps
  legality and commutes with the change of every count.
* Definition 2.7: a schedule of slots, with the slot support
  `T = LinearTime(N)`, the boundary support `I = LinearTime(N + 1)`, the phase
  of each slot read from a pointed clock, and the checkpoints, an
  order-preserving selection of boundaries.
* Definition 2.8: a control tapestry, a rectangular tapestry over the slot
  support whose rows prescribe the open phase, when there is one, and other
  control values that rules may read.
* Definition 2.9: an execution, or run, of a performance; its trajectory, the
  states at the checkpoints; and a trace, a retained record of selected
  events.
-/

namespace Artform

/-! ## Definition 2.3: contracts -/

/-- **Definition 2.3** (contract). A contract for a stretch of a performance
between two checkpoints states what must hold at its first checkpoint, what it
guarantees at its last, and an invariant, a condition on states that it keeps
at every checkpoint of the stretch. -/
@[book "def:contract"]
structure Contract (State : Type) where
  /-- What must hold at the first checkpoint. -/
  requires : State → Prop
  /-- What it guarantees at the last checkpoint. -/
  guarantees : State → Prop
  /-- The invariant it keeps at every checkpoint. -/
  invariant : State → Prop

namespace Contract

variable {State : Type}

/-- **Definition 2.3** (composition of contracts): two contracts compose when
the guarantee of the first gives what the second requires at their shared
checkpoint. -/
@[book "def:contract"]
def Compose (c d : Contract State) : Prop := ∀ x, c.guarantees x → d.requires x

/-- A stretch with the checkpoint states `x₀, …, x_m` keeps the contract: if
its first state meets the requirement, then its last state meets the
guarantee and every state meets the invariant. -/
def KeptBy (c : Contract State) {m : ℕ} (x : Fin (m + 1) → State) : Prop :=
  c.requires (x 0) → c.guarantees (x (Fin.last m)) ∧ ∀ i, c.invariant (x i)

end Contract

/-! ## Definition 2.4: symmetries of a dance -/

/-- **Definition 2.4** (symmetry of a dance). For a dance whose states satisfy
`Legal` and whose count `j` makes the change `F j`, a symmetry is a script `r`
on its states that carries legal states to legal states and commutes with the
change of each count: `r · F_j(x) = F_j(r · x)` for every count `j` and every
legal state `x`. -/
@[book "def:dance-symmetry"]
def IsDanceSymmetry {State Count : Type} (Legal : State → Prop) (F : Count → State → State)
    (r : State → State) : Prop :=
  (∀ x, Legal x → Legal (r x)) ∧ ∀ j x, Legal x → r (F j x) = F j (r x)

/-! ## Definitions 2.7 and 2.8: slots, phases, checkpoints and control -/

/-- **Definition 2.7** (slots, phases and checkpoints). A performance scheduled
in `N` slots, each an occasion for work of one kind. Slot `t` runs from
boundary `t` to boundary `t + 1`. The phase of a slot is the kind of work it
opens, read from a pointed clock over the slots. The checkpoints are the
boundaries at which the state is read and declared conditions must hold,
fixed by an order-preserving selection `b` of boundaries. -/
@[book "def:slots-phases"]
structure SlotSchedule where
  /-- The number `N` of slots. -/
  N : ℕ
  /-- The pointed clock over the slots: its phases are the kinds of work. -/
  clock : PointedCycle
  /-- The number of checkpoints. -/
  m : ℕ
  /-- The checkpoints, an order-preserving selection of boundaries. -/
  b : Fin m ↪o Fin (N + 1)

namespace SlotSchedule

variable (S : SlotSchedule)

/-- **Definition 2.7** (slot support): `T = LinearTime(N)`. -/
@[book "def:slots-phases"]
abbrev slots : TimeForm := LinearTime S.N

/-- **Definition 2.7** (boundary support): `I = LinearTime(N + 1)`. -/
@[book "def:slots-phases"]
abbrev boundaries : TimeForm := LinearTime (S.N + 1)

/-- The boundary at which slot `t` begins, `t`. -/
def opening (t : Fin S.N) : Fin (S.N + 1) := t.castSucc

/-- The boundary at which slot `t` ends, `t + 1`. -/
def closing (t : Fin S.N) : Fin (S.N + 1) := t.succ

/-- **Definition 2.7** (phase of a slot): the kind of work slot `t` opens, read
from the pointed clock over the slots, which begins at its base phase and
advances one phase each slot. -/
@[book "def:slots-phases"]
def phase (t : Fin S.N) : S.clock.time.cells := S.clock.base + Fin.ofNat S.clock.n t

end SlotSchedule

/-- **Definition 2.8** (control tapestry). A rectangular tapestry over the slot
support `LinearTime(N)` whose rows prescribe, slot by slot, the phase that is
open and other control values, such as cues, that rules may read. When the
slots open different kinds of work, one row is the row of phases; a
performance whose slots all open the same kind of work needs none. It says
when each kind of work is eligible, and holds no record of which eligible
change is made. -/
@[book "def:control-tapestry"]
structure ControlTapestry (N : ℕ) where
  /-- The control rows over the slot support. -/
  rows : RectTapestry (LinearTime N)
  /-- The row of phases, if the slots open different kinds of work. -/
  phaseRow : Option rows.R.cells

/-! ## Definition 2.9: executions, trajectories and traces -/

/-- **Definition 2.9** (execution, or run). A performance of `N` counts as the
rules carry it out: the changes made count by count from the opening state,
with the states they pass through. It keeps the state after each count,
`state 0` being the opening state, and the rules applied at each count, in
the order applied. -/
@[book "def:trajectory-trace"]
structure PerformanceRun (State Rule : Type) (N : ℕ) where
  /-- The opening state, and the state after each count. -/
  state : Fin (N + 1) → State
  /-- The rules applied at each count, in order. -/
  applied : Fin N → List Rule

/-- An event of a trace: a rule applied at a count. -/
structure TraceEvent (Rule : Type) (N : ℕ) where
  /-- The rule applied. -/
  rule : Rule
  /-- The count at which it was applied. -/
  count : Fin N

/-- **Definition 2.9** (trace). A retained record of selected events: which
rules were applied, at which count, and in what order, the list keeping the
order; where waiting must stay recoverable, it also keeps boundary records. -/
@[book "def:trajectory-trace"]
structure Trace (Rule : Type) (N : ℕ) where
  /-- The selected events, in order. -/
  events : List (TraceEvent Rule N)
  /-- The boundary records. -/
  boundaries : List (Fin (N + 1))

namespace PerformanceRun

variable {State Rule : Type} {N : ℕ} (e : PerformanceRun State Rule N)

/-- **Definition 2.9** (trajectory): the sequence of the states of an execution
at the checkpoints `b`, what the dance did. -/
@[book "def:trajectory-trace"]
def trajectory {m : ℕ} (b : Fin m ↪o Fin (N + 1)) : Fin m → State := fun k => e.state (b k)

/-- Every event of the execution, count by count, in the order applied. -/
def events : List (TraceEvent Rule N) :=
  (List.finRange N).flatMap fun j => (e.applied j).map fun r => ⟨r, j⟩

/-- A trace of the execution: its events are selected from the execution's
events, in their order. -/
def HasTrace (τ : Trace Rule N) : Prop := τ.events.Sublist e.events

end PerformanceRun

/-! ## Non-vacuity -/

/-- Two executions with the same trajectory and different traces: after a
count that changes nothing, by the rule `0` in one and the rule `1` in the
other. -/
example :
    let e₀ : PerformanceRun Unit ℕ 1 := ⟨fun _ => (), fun _ => [0]⟩
    let e₁ : PerformanceRun Unit ℕ 1 := ⟨fun _ => (), fun _ => [1]⟩
    e₀.trajectory (OrderIso.refl _).toOrderEmbedding =
        e₁.trajectory (OrderIso.refl _).toOrderEmbedding ∧
      e₀.events ≠ e₁.events := by
  refine ⟨rfl, ?_⟩
  simp [PerformanceRun.events, List.finRange_succ]

/-- Two contracts that compose: the first guarantees what the second
requires. -/
example : (⟨fun _ => True, (· = 1), fun _ => True⟩ : Contract ℕ).Compose
    ⟨(· = 1), (· = 2), fun _ => True⟩ :=
  fun _ h => h

end Artform
