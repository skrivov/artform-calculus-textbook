import Mathlib.Data.Fintype.EquivFin
import ArtformTextbook.Ch05.Defs.Realizers

/-!
# Laws in steps (Section 5.5)

Definition 5.12: a law whose moves each belong to one of finitely many steps,
with a score that opens one step in every slot, and invariants that are
checked at their checkpoints; and the deterministic realizers of such a law
that are well posed.

**Slots and boundaries** (Definition 2.7). Slot `t` runs from boundary `t` to
boundary `t + 1`; boundary `0` opens the score. A checkpoint is a boundary at
which declared conditions must hold.

**Legal at a boundary.** A law in steps checks each invariant only at its
checkpoints, and between them the invariant may fail: the native blocks of
Chapter 8 keep their constraint only at block boundaries, with many slots
between. So a state at boundary `t` is *legal there* when every invariant
whose checkpoints include `t` holds. Definition 5.9 asks that each move lead
to a legal state, and Definition 5.10 that each batch a realizer selects keep
the invariants; for a law in steps both are read at boundaries: from a state
legal at boundary `t`, a move of the step open in slot `t`, and the batch the
realizer selects there, lead to a state legal at boundary `t + 1`. A law of
Section 5.4 is the case of one step, open in every slot, with every invariant
checked at every boundary (`Law.inSteps`).
-/

namespace Artform

variable {A : Presentation}

/-- **Definition 5.12** (score). The control tapestry of a law in steps
(Definition 2.8): its rows say, slot by slot, which step is open and whether
the score allows an empty batch there. The score repeats: one pass through
its repeating pattern, `period` slots long, is a tick. -/
@[book "def:law-steps"]
structure Score (Step : Type) where
  /-- The step open in each slot. -/
  opens : ℕ → Step
  /-- The slots in which the score allows an empty batch. -/
  allowsEmpty : ℕ → Prop
  /-- The number of slots in one pass through the repeating pattern: a tick. -/
  period : ℕ
  period_pos : 0 < period
  /-- Every tick opens the same steps in the same order. -/
  repeats : ∀ t, opens (t + period) = opens t ∧ (allowsEmpty (t + period) ↔ allowsEmpty t)

/-- **Definition 5.12** (checkpoint). An invariant of a law in steps: a
condition on the tables, with its checkpoints, the boundaries at which it
must hold. Boundary `t + 1` closes slot `t`. -/
@[book "def:law-steps"]
structure CheckedInvariant (A : Presentation) where
  /-- The condition. -/
  holds : A.Table → Prop
  /-- Its checkpoints. -/
  checkpoints : Set ℕ

/-- **Definition 5.12** (law in steps). A law (Definition 5.9) whose moves each
belong to one of finitely many steps, with a score that says, slot by slot,
which step is open; only the moves of the open step are enabled. Each
invariant comes with its checkpoints. Each move of the step open in slot `t`,
enabled at a state legal at boundary `t`, leads to a state legal at boundary
`t + 1`: Definition 5.9's condition, read at the checkpoints. -/
@[book "def:law-steps"]
structure LawInSteps (A : Presentation) where
  /-- The steps. -/
  Step : Type
  /-- There are finitely many steps. -/
  [finiteStep : Finite Step]
  /-- The moves of each step, written as process profiles. -/
  moves : Step → List (ProcessProfile A)
  /-- The invariants, each with its checkpoints. -/
  invariants : List (CheckedInvariant A)
  /-- The score. -/
  score : Score Step
  /-- Each move of the open step leads from a state legal at the slot's opening
  boundary to one legal at its closing boundary. -/
  moves_legal : ∀ (t : ℕ) (x : A.Table), (∀ J ∈ invariants, t ∈ J.checkpoints → J.holds x) →
    ∀ u ∈ moves (score.opens t), u.guard x →
      ∀ J ∈ invariants, t + 1 ∈ J.checkpoints → J.holds (u.apply x)

attribute [instance] LawInSteps.finiteStep

namespace LawInSteps

/-- A state legal at boundary `t`: every invariant checked at `t` holds there. -/
def LegalAt (L : LawInSteps A) (t : ℕ) (x : A.Table) : Prop :=
  ∀ J ∈ L.invariants, t ∈ J.checkpoints → J.holds x

/-- The batches the law allows in slot `t`: batches of enabled moves of the
step that the score opens there. -/
def AllowsAt (L : LawInSteps A) (t : ℕ) {x : A.Table} (b : Batch A x) : Prop :=
  ∀ a ∈ b.apps, a.profile ∈ L.moves (L.score.opens t)

/-- **Definition 5.10** (realizer), deterministic, for a law in steps: one batch
in every slot at every state, with the evidence that at a state legal at the
slot's opening boundary the batch is made of moves of the open step and leads
to a state legal at the slot's closing boundary. The choice is written for
every table; only its values at legal states matter. -/
@[book "def:realizer"]
structure DetRealizer (L : LawInSteps A) where
  /-- The batch selected in each slot at each state. -/
  select : ℕ → (x : A.Table) → Batch A x
  allows : ∀ t x, L.LegalAt t x → L.AllowsAt t (select t x)
  keeps : ∀ t x, L.LegalAt t x → L.LegalAt (t + 1) (select t x).apply

/-- **Definition 5.12** (well-posed realizer). A deterministic realizer of a law
in steps is well posed when it is *total*, selecting a nonempty batch at every
legal state and open step except where the score allows an empty one, and
*order-free*: applying the moves of a selected batch in any order gives the
same state. -/
@[book "def:law-steps"]
structure DetRealizer.WellPosed {L : LawInSteps A} (R : L.DetRealizer) : Prop where
  total : ∀ t x, L.LegalAt t x → ¬ L.score.allowsEmpty t → (R.select t x).apps ≠ []
  orderFree : ∀ t x, L.LegalAt t x → ∀ l : List (EnabledApp A x),
    l.Perm (R.select t x).apps → applyAll l x = (R.select t x).apply

end LawInSteps

/-- A run that follows a realizer of a law in steps over the stretch of the
score that begins at slot `s`: step `i` applies the batch the realizer
selects in slot `s + i`, at the state where the step begins. -/
def Run.Follows {L : LawInSteps A} (R : L.DetRealizer) (s : ℕ) {n : ℕ} (r : Run A n) : Prop :=
  ∀ i : Fin n, r.batch i = R.select (s + i) (r.state i.castSucc)

/-! ## A law of Section 5.4 is a law in steps

One step, open in every slot, every invariant checked at every boundary, and
an empty batch allowed everywhere. -/

/-- A law of Section 5.4 as a law in steps. -/
def Law.inSteps (L : Law A) : LawInSteps A where
  Step := Unit
  moves _ := L.profiles
  invariants := L.invariants.map fun J => ⟨J, Set.univ⟩
  score := ⟨fun _ => (), fun _ => True, 1, Nat.one_pos, fun _ => ⟨rfl, Iff.rfl⟩⟩
  moves_legal t x hx u hu hg J hJ _ := by
    obtain ⟨J', hJ', rfl⟩ := List.mem_map.1 hJ
    exact L.moves_legal x (fun K hK => hx ⟨K, Set.univ⟩ (List.mem_map_of_mem hK) (Set.mem_univ t))
      u hu hg J' hJ'

theorem Law.inSteps_legalAt (L : Law A) (t : ℕ) (x : A.Table) :
    L.inSteps.LegalAt t x ↔ L.Legal x :=
  ⟨fun h J hJ => h ⟨J, Set.univ⟩ (List.mem_map_of_mem hJ) (Set.mem_univ t), fun h J hJ _ => by
    obtain ⟨J', hJ', rfl⟩ := List.mem_map.1 (show J ∈ L.invariants.map _ from hJ)
    exact h J' hJ'⟩

/-- A deterministic realizer of a law of Section 5.4, as a realizer of the law
in steps: it selects the same batch in every slot. -/
def DetRealizer.inSteps {L : Law A} (R : DetRealizer L) : L.inSteps.DetRealizer where
  select _ := R.select
  allows t x hx a ha := R.allows x ((L.inSteps_legalAt t x).1 hx) a ha
  keeps t x hx := (L.inSteps_legalAt (t + 1) _).2 (R.keeps x ((L.inSteps_legalAt t x).1 hx))

end Artform
