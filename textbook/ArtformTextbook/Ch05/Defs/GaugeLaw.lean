import Mathlib.Data.Multiset.Defs
import ArtformTextbook.Ch05.Defs.Realizers
import ArtformTextbook.Ch05.Defs.Steps

/-!
# Gauge-covariant laws and realizers (Section 5.15, Definition 5.35)

A gauge change acts on the states of a gauge frame: on the links of the
connection, in link coordinates, by `U_e ↦ h_{t(e)} U_e h_{s(e)}⁻¹`
(`eq:gauge-action`); at each vertex `v` by `h_v` (a pose by `g_v ↦ h_v g_v`, a
matter value by `ψ_v ↦ ρ(h_v) ψ_v`); and on the further fields by a declared
action. Each of these acts on the value at one position at a time. Lean takes
the action as data, `GaugeAction`: for every gauge change and every position of
the frame, a map of the values allowed there. Definition 5.35 uses nothing else
about it.

A move of a law is a process profile (Definition 5.9), and a batch lists its
enabled applications in one order (Definition 2.6). Two batches are compared
through their moves, as families: the same moves, in any order.

The definition is stated for the laws of Definition 5.9 (`Law`) and their
realizers, and for the laws in steps of Definition 5.12 (`LawInSteps`) and
their deterministic realizers; the conditions on moves and invariants
(`GaugeAction.CovariantLaw`) can also be checked of a law given by its parts.
-/

namespace Artform

variable {A : Presentation} {𝒢 : Type*}

/-- **Definition 5.35** (the setting: a gauge change acting on the states of a
gauge frame), position by position: `act h p` is what the gauge change `h`
does to the value at the position `p`. In a gauge frame it is
`U_e ↦ h_{t(e)} U_e h_{s(e)}⁻¹` at a link of the connection
(`eq:gauge-action`), `h_v` at a field at the vertex `v` (a pose by
`g_v ↦ h_v g_v`, a matter value by `ψ_v ↦ ρ(h_v) ψ_v`), and the declared
action at a further field. Lean takes the action as data and does not restrict
it to these forms. -/
@[book "def:gauge-covariant-law"]
structure GaugeAction (A : Presentation) (𝒢 : Type*) where
  /-- What the gauge change `h` does to the value at the position `p`. -/
  act : 𝒢 → (p : A.P) → A.V p → A.V p

namespace GaugeAction

variable (α : GaugeAction A 𝒢)

/-- `h · x`: the gauge change `h` applied at every position of the table `x`. -/
def smul (h : 𝒢) (x : A.Table) : A.Table := fun p => α.act h p (x p)

@[simp]
theorem smul_apply (h : 𝒢) (x : A.Table) (p : A.P) : α.smul h x p = α.act h p (x p) := rfl

/-- **Definition 5.35**, the first condition, for one move: for every gauge
change `h` and every state `x`, if the move is enabled at `x`, then it is
enabled at `h · x`, and its proposal there is `h` applied to its proposal at
`x`, at every position of its write footprint. A move is a process profile,
whose footprints do not depend on the state, so it has the same footprints at
`x` and at `h · x`. -/
@[book "def:gauge-covariant-law"]
def CovariantMove (u : ProcessProfile A) : Prop :=
  ∀ (h : 𝒢) (x : A.Table), u.guard x →
    u.guard (α.smul h x) ∧ ∀ p ∈ u.writes, u.update (α.smul h x) p = α.act h p (u.update x p)

/-- **Definition 5.35**, the second condition: for every gauge change `h` and
every state `x`, the invariants hold at `x` exactly when they hold at
`h · x`. -/
@[book "def:gauge-covariant-law"]
def CovariantInvariants (I : List (A.Table → Prop)) : Prop :=
  ∀ (h : 𝒢) (x : A.Table), (∀ J ∈ I, J x) ↔ ∀ J ∈ I, J (α.smul h x)

/-- **Definition 5.35** (gauge-covariant law), for a law given by its
invariants and its moves: each move is covariant (`CovariantMove`), and the
invariants hold at `x` exactly when they hold at `h · x`
(`CovariantInvariants`). A law in steps (Definition 5.12) is given this way
too; its steps and score play no part in either condition. -/
@[book "def:gauge-covariant-law"]
structure CovariantLaw (invariants : List (A.Table → Prop))
    (moves : List (ProcessProfile A)) : Prop where
  /-- Each move enabled at `x` is enabled at `h · x`, with the same
  footprints, and its proposal there is `h` applied to its proposal at `x`. -/
  moves : ∀ u ∈ moves, α.CovariantMove u
  /-- The invariants hold at `x` exactly when they hold at `h · x`. -/
  invariants : α.CovariantInvariants invariants

end GaugeAction

/-- **Definition 5.35** (gauge-covariant law). A law on a gauge frame is gauge
covariant when, for every gauge change `h` and every state `x`, each move
enabled at `x` is also enabled at `h · x`, with the same footprints, and its
proposal there is `h` applied to its proposal at `x`; and the law's
invariants hold at `x` exactly when they hold at `h · x`. -/
@[book "def:gauge-covariant-law"]
def Law.GaugeCovariant (L : Law A) (α : GaugeAction A 𝒢) : Prop :=
  α.CovariantLaw L.invariants L.profiles

/-- The moves of a batch: the process profiles of its applications, in the
order the batch lists them. -/
def Batch.moves {x : A.Table} (b : Batch A x) : List (ProcessProfile A) :=
  b.apps.map EnabledApp.profile

namespace GaugeAction

variable (α : GaugeAction A 𝒢)

/-- Selecting at `h · x` the same batch as at `x`, for every gauge change `h`
and every state `x` that `legal` admits: the same moves, in any order. -/
def SameBatch (legal : A.Table → Prop) (select : (x : A.Table) → Batch A x) : Prop :=
  ∀ (h : 𝒢) (x : A.Table), legal x → (select (α.smul h x)).moves.Perm (select x).moves

/-- Allowing at `h · x` the same set of batches as at `x`, for every gauge
change `h` and every state `x` that `legal` admits; each batch is taken as the
family of its moves. -/
def SameBatches (legal : A.Table → Prop) (allowed : (x : A.Table) → Batch A x → Prop) :
    Prop :=
  ∀ (h : 𝒢) (x : A.Table), legal x →
    {m : Multiset (ProcessProfile A) | ∃ b, allowed (α.smul h x) b ∧ (b.moves : Multiset _) = m} =
      {m | ∃ b, allowed x b ∧ (b.moves : Multiset _) = m}

/-- Attaching at `h · x` the same weights as at `x`, for every gauge change `h`
and every state `x` that `legal` admits: a batch at `h · x` carries the weight
of the batch at `x` with the same moves, and a batch carries a weight other
than `0` at one of the two states only if the other state has a batch with the
same moves. The weights may be numbers, as for a stochastic realizer, or the
coefficients of a coherent realizer. -/
structure SameWeights {W : Type*} [Zero W] (legal : A.Table → Prop)
    (w : (x : A.Table) → Batch A x → W) : Prop where
  /-- Batches with the same moves carry the same weight. -/
  eq : ∀ (h : 𝒢) (x : A.Table), legal x → ∀ (b : Batch A x) (b' : Batch A (α.smul h x)),
    b'.moves.Perm b.moves → w (α.smul h x) b' = w x b
  /-- A batch of weight other than `0` at `x` has its counterpart at `h · x`. -/
  forth : ∀ (h : 𝒢) (x : A.Table), legal x → ∀ b : Batch A x, w x b ≠ 0 →
    ∃ b' : Batch A (α.smul h x), b'.moves.Perm b.moves
  /-- A batch of weight other than `0` at `h · x` has its counterpart at `x`. -/
  back : ∀ (h : 𝒢) (x : A.Table), legal x → ∀ b' : Batch A (α.smul h x),
    w (α.smul h x) b' ≠ 0 → ∃ b : Batch A x, b'.moves.Perm b.moves

end GaugeAction

variable {L : Law A}

/-- **Definition 5.35** (gauge-covariant realizer), deterministic: at every
legal state `x` and for every gauge change `h`, it selects at `h · x` the same
batch as at `x`. -/
@[book "def:gauge-covariant-law"]
def DetRealizer.GaugeCovariant (R : DetRealizer L) (α : GaugeAction A 𝒢) : Prop :=
  α.SameBatch L.Legal R.select

/-- **Definition 5.35** (gauge-covariant realizer), relational: at every legal
state `x` and for every gauge change `h`, it allows at `h · x` the same set of
batches as at `x`. -/
@[book "def:gauge-covariant-law"]
def RelRealizer.GaugeCovariant (R : RelRealizer L) (α : GaugeAction A 𝒢) : Prop :=
  α.SameBatches L.Legal R.allowed

/-- **Definition 5.35** (gauge-covariant realizer), stochastic: at every legal
state `x` and for every gauge change `h`, it gives the batches at `h · x` the
same weights as at `x`. -/
@[book "def:gauge-covariant-law"]
def StochRealizer.GaugeCovariant (R : StochRealizer L) (α : GaugeAction A 𝒢) : Prop :=
  α.SameWeights L.Legal R.weight

/-- **Definition 5.35** (gauge-covariant law), for a law in steps
(Definition 5.12): for every gauge change `h` and every state `x`, each move of
every step that is enabled at `x` is enabled at `h · x`, with the same
footprints, and its proposal there is `h` applied to its proposal at `x`; and
at every boundary, `x` is legal exactly when `h · x` is. The score plays no
part. -/
@[book "def:gauge-covariant-law"]
structure LawInSteps.GaugeCovariant (L : LawInSteps A) (α : GaugeAction A 𝒢) : Prop where
  /-- Each move of each step is gauge covariant. -/
  moves : ∀ σ, ∀ u ∈ L.moves σ, α.CovariantMove u
  /-- The invariants checked at each boundary hold at `x` exactly when they hold at
  `h · x`. -/
  invariants : ∀ (h : 𝒢) (x : A.Table) (t : ℕ), L.LegalAt t x ↔ L.LegalAt t (α.smul h x)

/-- **Definition 5.35** (gauge-covariant realizer), deterministic, for a law in
steps: in every slot, at every state legal at the slot's opening boundary and
for every gauge change `h`, it selects at `h · x` the same batch as at `x`. -/
@[book "def:gauge-covariant-law"]
def LawInSteps.DetRealizer.GaugeCovariant {L : LawInSteps A} (R : L.DetRealizer)
    (α : GaugeAction A 𝒢) : Prop :=
  ∀ t, α.SameBatch (L.LegalAt t) (R.select t)

end Artform
