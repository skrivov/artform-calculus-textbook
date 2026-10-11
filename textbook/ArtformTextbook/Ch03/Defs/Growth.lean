import Mathlib.Algebra.Group.End
import Mathlib.Data.Finset.Card
import ArtformTextbook.Ch05.Defs.Realizers

/-!
# Positive generation: patches, attachments, policies and fairness (Sections 3.8–3.9)

Growth is read in the process model of Section 2.5, as the book does in
Section 3.8: an attachment rule is a process profile read at a patch.

* **Patches.** The frame of patches has one position for every ambient cell,
  holding whether the cell is present; a table is a patch, the set of cells
  present, and `X ≤ Y` says that every cell of `X` is a cell of `Y`. Cells
  keep their ambient identities, so attaching a cell that is already present
  changes nothing: the literal union of Section 3.8.
* **Attachments.** A located attachment is a process profile on patches
  whose guard is the validity of its trigger's placement, whose read
  footprint is the placement's image and whose write footprint is the cells
  it attaches; its update proposal makes those cells present (`Attaches`), so
  making it gives `X ∪ W_p`. A rule is the set of its located attachments, one
  for each placement. A positive trigger is extension-stable (`Persistent`):
  valid in a patch, it stays valid in every larger patch.
* **Runs.** A run of `n` steps is a `Run` (Definition 5.10's trajectory with
  its trace of batches); a continuing execution is an `Execution`, with a
  state at every boundary and a batch at every slot.
* **Control.** The rules come with phases, and the control tapestry's row
  says which phase is open in each slot (Definitions 2.7 and 2.8).
-/

namespace Artform

/-- The frame of the patches of an ambient cell scheme (Section 3.8): a
position for every ambient cell, holding whether the cell is present. A table
is a patch; `X ≤ Y` says that every cell of `X` is a cell of `Y`. -/
abbrev patchFrame (Cell : Type) : Presentation := ⟨Cell, fun _ => Prop⟩

variable {Cell : Type}

namespace ProcessProfile

/-- An attachment (Section 3.8): its update proposal makes every cell of its
write footprint present, so that making it attaches those cells,
`X ↦ X ∪ W_p`. -/
def Attaches (u : ProcessProfile (patchFrame Cell)) : Prop :=
  ∀ X, ∀ c ∈ u.writes, u.update X c

/-- A positive, extension-stable trigger (Section 3.8): a placement valid in a
patch stays valid in every larger patch. -/
def Persistent (u : ProcessProfile (patchFrame Cell)) : Prop :=
  ∀ X Y : (patchFrame Cell).Table, X ≤ Y → u.guard X → u.guard Y

end ProcessProfile

/-- A closed patch (Section 3.9): every attachment of the rules that is enabled
there finds its cells present already. -/
def Closed (R : Set (ProcessProfile (patchFrame Cell))) (X : (patchFrame Cell).Table) : Prop :=
  ∀ u ∈ R, u.guard X → ∀ c ∈ u.writes, X c

/-- Making every enabled attachment of the rules at once: a cell is present
after the step when it was present before or some enabled attachment
attaches it. When every attachment of the rules has its outputs in a window
`W`, this is the book's `F_W` (Section 3.9). -/
def attachAll (R : Set (ProcessProfile (patchFrame Cell))) (X : (patchFrame Cell).Table) :
    (patchFrame Cell).Table :=
  fun c => X c ∨ ∃ u ∈ R, u.guard X ∧ c ∈ u.writes

/-- The patches that some run of the rules reaches from the seed `X₀` in `n`
steps: each step makes a batch, possibly empty, of enabled attachments of
the rules. -/
def reachable (R : Set (ProcessProfile (patchFrame Cell))) (X₀ : (patchFrame Cell).Table)
    (n : ℕ) : Set (patchFrame Cell).Table :=
  {X | ∃ r : Run (patchFrame Cell) n, r.state 0 = X₀ ∧
    (∀ i, ∀ a ∈ (r.batch i).apps, a.profile ∈ R) ∧ r.state (Fin.last n) = X}

/-! ## Motions -/

/-- A motion `s` of the canvas, a permutation of its cells, carries a patch `X`
to `s(X)`: the cell `c` is in `s(X)` when `s⁻¹(c)` is in `X`. -/
def movePatch (s : Equiv.Perm Cell) (X : (patchFrame Cell).Table) : (patchFrame Cell).Table :=
  fun c => X (s.symm c)

/-- A motion `s` carries a process profile on patches to the profile that does
the same at the moved cells: its guard holds at `X` when the original holds at
`s⁻¹(X)`, and its footprints are the images of the original's. -/
def moveProfile (s : Equiv.Perm Cell) (u : ProcessProfile (patchFrame Cell)) :
    ProcessProfile (patchFrame Cell) where
  guard X := u.guard fun c => X (s c)
  reads := s.symm ⁻¹' u.reads
  writes := s.symm ⁻¹' u.writes
  update X c := u.update (fun d => X (s d)) (s.symm c)
  guard_reads X Y h := u.guard_reads _ _ fun p hp => h (s p) (by simpa using hp)
  update_reads X Y h c hc := u.update_reads _ _ (fun p hp => h (s p) (by simpa using hp)) _ hc

/-! ## Policies and continuing executions -/

/-- **Definition 3.28** (policy). A complete assignment that gives each state,
together with a memory of its own, one batch of the applications enabled
there, possibly empty; and the memory it keeps for the next step. It is the
only thing in a run that chooses. -/
@[book "def:policy"]
structure Policy (A : Presentation) (Mem : Type) where
  /-- The batch chosen at each state, with the memory. -/
  choose : (x : A.Table) → Mem → Batch A x
  /-- The memory kept for the next step. -/
  remember : A.Table → Mem → Mem

/-- A continuing execution: a state at every boundary, and the batch made in
every slot, each step making its batch. -/
structure Execution (A : Presentation) where
  /-- The state at each boundary. -/
  state : ℕ → A.Table
  /-- The batch made in each slot. -/
  batch : (t : ℕ) → Batch A (state t)
  /-- Each step makes its batch. -/
  step : ∀ t, state (t + 1) = (batch t).apply

namespace Policy

variable {A : Presentation} {Mem : Type}

/-- The states and memories of a policy's run from `x₀` with memory `m₀`. -/
noncomputable def trajectory (π : Policy A Mem) (x₀ : A.Table) (m₀ : Mem) : ℕ → A.Table × Mem
  | 0 => (x₀, m₀)
  | t + 1 =>
    ((π.choose (π.trajectory x₀ m₀ t).1 (π.trajectory x₀ m₀ t).2).apply,
      π.remember (π.trajectory x₀ m₀ t).1 (π.trajectory x₀ m₀ t).2)

/-- The continuing execution that a scheduler carries out under a policy: at
each step it lets the policy choose a batch, and makes it. -/
noncomputable def execution (π : Policy A Mem) (x₀ : A.Table) (m₀ : Mem) : Execution A where
  state t := (π.trajectory x₀ m₀ t).1
  batch t := π.choose _ (π.trajectory x₀ m₀ t).2
  step _ := rfl

end Policy

/-- The control of an execution (Definitions 2.7 and 2.8): the rules, each with
the phase of the work it does, and the control tapestry's row of phases,
which says slot by slot which phase is open. -/
structure Control (A : Presentation) where
  /-- The phases. -/
  Phase : Type
  /-- The rules. -/
  rules : Set (ProcessProfile A)
  /-- The phase of each rule. -/
  phase : ProcessProfile A → Phase
  /-- The phase open in each slot. -/
  opens : ℕ → Phase

namespace Control

variable {A : Presentation}

/-- An offer to the rule `u` is a slot whose open phase lets it be selected. -/
def Offered (C : Control A) (u : ProcessProfile A) (t : ℕ) : Prop := C.opens t = C.phase u

end Control

namespace Execution

variable {A : Presentation}

/-- The execution runs under the control: each batch is made of applications
of the rules whose phase is open in its slot. -/
def Under (r : Execution A) (C : Control A) : Prop :=
  ∀ t, ∀ a ∈ (r.batch t).apps, a.profile ∈ C.rules ∧ C.Offered a.profile t

/-- The rule `u` is selected in slot `t`: the batch made there has an
application of `u`. -/
def Selected (r : Execution A) (u : ProcessProfile A) (t : ℕ) : Prop :=
  ∃ a ∈ (r.batch t).apps, a.profile = u

/-- **Definition 3.30** (cadence fairness). The control tapestry keeps opening
every phase that pending work needs: whenever a rule is enabled and has not
yet been selected, its phase is open in that slot or a later one. Work is
pending from the slot at which it is enabled until the policy selects it. -/
@[book "def:fairness"]
def CadenceFair (r : Execution A) (C : Control A) : Prop :=
  ∀ u ∈ C.rules, ∀ t, u.guard (r.state t) → (∀ s < t, ¬ r.Selected u s) →
    ∃ t' ≥ t, C.Offered u t'

/-- **Definition 3.30** (application fairness). The policy eventually selects
every application that stays enabled each time its phase is open: if the rule
`u` has not been selected before slot `t`, is enabled in every slot from `t` on
in which its phase is open, and its phase keeps opening, then `u` is selected
in some slot from `t` on. -/
@[book "def:fairness"]
def ApplicationFair (r : Execution A) (C : Control A) : Prop :=
  ∀ u ∈ C.rules, ∀ t, (∀ s < t, ¬ r.Selected u s) →
    (∀ t' ≥ t, C.Offered u t' → u.guard (r.state t')) →
    (∀ t₁, ∃ t' ≥ t₁, C.Offered u t') → ∃ t' ≥ t, r.Selected u t'

open Classical in
/-- **Definition 3.31** (bounded windowed progress), for positive integers `b`,
`c` and a nonnegative integer `k`. For every rule `u` pending at an offer `t₀`
(offered while enabled, and not yet selected), whose guard stays valid until
`u` is selected: while `u` waits, the next offer comes within `c` slots; and
`u` is made in a slot `t'` such that fewer than `b` of its offers from `t₀` on
come more than `k` slots before `t'`. That is, the policy serves `u` by its
`b`th offer and makes it within a further `k` slots; an execution makes the
batch it selects in its slot, so it records when `u` is made. -/
@[book "def:windowed-progress"]
def WindowedProgress (r : Execution A) (C : Control A) (b c k : ℕ) : Prop :=
  0 < b ∧ 0 < c ∧
  ∀ u ∈ C.rules, ∀ t₀, C.Offered u t₀ → u.guard (r.state t₀) → (∀ s < t₀, ¬ r.Selected u s) →
    (∀ t ≥ t₀, (∀ s < t, ¬ r.Selected u s) → u.guard (r.state t)) →
    (∀ t ≥ t₀, (∀ s ≤ t, ¬ r.Selected u s) → ∃ t', t < t' ∧ t' ≤ t + c ∧ C.Offered u t') ∧
    ∃ t', t₀ ≤ t' ∧ r.Selected u t' ∧
      ((Finset.range (t' - k)).filter fun s => t₀ ≤ s ∧ C.Offered u s).card < b

end Execution

end Artform
