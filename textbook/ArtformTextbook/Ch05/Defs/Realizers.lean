import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Fin.Basic
import ArtformTextbook.Ch02.Defs.Process

/-!
# Laws, realizers and runs (Section 5.4)

A law says which moves are allowed; a realizer says which allowed moves are
made; a run records what did happen.
-/

namespace Artform

open scoped NNReal

variable {A : Presentation}

/-- **Definition 5.9** (law; move; legal state). A law on a frame declares
finitely many conditions on its tables, its invariants, and finitely many
process profiles, its moves. The tables that satisfy every invariant are its
legal states. At a legal state each enabled move leads to a legal state. -/
@[book "def:law"]
structure Law (A : Presentation) where
  /-- The invariants. -/
  invariants : List (A.Table → Prop)
  /-- The moves, written as process profiles. -/
  profiles : List (ProcessProfile A)
  /-- Each move allowed at a legal state leads to a legal state. -/
  moves_legal : ∀ x : A.Table, (∀ J ∈ invariants, J x) →
    ∀ u ∈ profiles, u.guard x → ∀ J ∈ invariants, J (u.apply x)

namespace Law

/-- A legal state: a table that satisfies every invariant. -/
def Legal (L : Law A) (x : A.Table) : Prop := ∀ J ∈ L.invariants, J x

/-- The batches a law allows at a table: batches of enabled applications of
its moves. -/
def Allows (L : Law A) {x : A.Table} (b : Batch A x) : Prop :=
  ∀ a ∈ b.apps, a.profile ∈ L.profiles

end Law

/-- **Definition 5.10** (realizer), deterministic: one batch at every legal
state, with the evidence that it is allowed and keeps the invariants. The
choice is written for every table; only its values at legal states matter. -/
@[book "def:realizer"]
structure DetRealizer (L : Law A) where
  /-- The batch selected at each state. -/
  select : (x : A.Table) → Batch A x
  allows : ∀ x, L.Legal x → L.Allows (select x)
  keeps : ∀ x, L.Legal x → L.Legal (select x).apply

/-- **Definition 5.10** (realizer), relational: a declared set of allowed
batches at every legal state, each allowed by the law and keeping its
invariants. -/
@[book "def:realizer"]
structure RelRealizer (L : Law A) where
  /-- The batches the realizer allows at each state. -/
  allowed : (x : A.Table) → Batch A x → Prop
  allows : ∀ x, L.Legal x → ∀ b, allowed x b → L.Allows b
  keeps : ∀ x, L.Legal x → ∀ b, allowed x b → L.Legal b.apply

/-- **Definition 5.10** (realizer), stochastic: weights on the batches, those
of positive weight at a legal state being allowed by the law and keeping its
invariants. -/
@[book "def:realizer"]
structure StochRealizer (L : Law A) where
  /-- The weight of each batch at each state. -/
  weight : (x : A.Table) → Batch A x → ℝ≥0
  allows : ∀ x, L.Legal x → ∀ b, weight x b ≠ 0 → L.Allows b
  keeps : ∀ x, L.Legal x → ∀ b, weight x b ≠ 0 → L.Legal b.apply

/-- **Definition 5.10** (run). A trajectory of states over `n` ticks, each step
applying a batch, together with the trace: the batches made. -/
@[book "def:realizer"]
structure Run (A : Presentation) (n : ℕ) where
  /-- The state at each tick. -/
  state : Fin (n + 1) → A.Table
  /-- The batch made at each step: the trace. -/
  batch : (i : Fin n) → Batch A (state i.castSucc)
  /-- Each step applies its batch. -/
  step : ∀ i : Fin n, state i.succ = (batch i).apply

namespace Run

variable {L : Law A} {n : ℕ}

/-- A run of a deterministic realizer: legal states, each step applying the
batch the realizer selects. -/
def OfDet (R : DetRealizer L) (r : Run A n) : Prop :=
  (∀ i, L.Legal (r.state i)) ∧ ∀ i, r.batch i = R.select (r.state i.castSucc)

/-- A run a relational realizer allows: legal states, each step applying a
batch the realizer allows. -/
def OfRel (R : RelRealizer L) (r : Run A n) : Prop :=
  (∀ i, L.Legal (r.state i)) ∧ ∀ i, R.allowed _ (r.batch i)

/-- A run of positive weight under a stochastic realizer: legal states, each
step applying a batch of positive weight. -/
def OfStoch (R : StochRealizer L) (r : Run A n) : Prop :=
  (∀ i, L.Legal (r.state i)) ∧ ∀ i, R.weight _ (r.batch i) ≠ 0

end Run

end Artform
