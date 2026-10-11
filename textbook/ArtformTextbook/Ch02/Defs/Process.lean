import Mathlib.Data.Set.Basic
import Mathlib.Order.Disjoint
import ArtformTextbook.Meta.Book

/-!
# Process profiles, enabled applications and batches (Section 2.5)

A frame presents its positions and the type of values allowed at each; a
table gives every position a value. A process profile is one kind of change
of tables, and a batch is a family of changes that may be made one after
another, in any order.
-/

namespace Artform

/-- The positions of a frame and the type of values allowed at each
(Definition 1.13; the formation lines write `A : Presentation`). -/
structure Presentation where
  /-- The positions. -/
  P : Type
  /-- The values allowed at each position. -/
  V : P → Type

/-- A table: one allowed value at every position. -/
abbrev Presentation.Table (A : Presentation) := (p : A.P) → A.V p

/-- **Definition 2.5** (process profile). One kind of change: a guard, the
condition under which it may act; a read footprint, the positions it may look
at; a write footprint, the positions it may change; and an update proposal,
the values it computes for its write footprint from what it reads. The guard
and the proposal look only at the read footprint. -/
@[book "def:process-profile"]
structure ProcessProfile (A : Presentation) where
  /-- The guard `G_p`. -/
  guard : A.Table → Prop
  /-- The read footprint `R_p`. -/
  reads : Set A.P
  /-- The write footprint `W_p`. -/
  writes : Set A.P
  /-- The update proposal `u_p`; only its values on `writes` are used. -/
  update : A.Table → A.Table
  guard_reads : ∀ x y : A.Table, (∀ p ∈ reads, x p = y p) → (guard x ↔ guard y)
  update_reads : ∀ x y : A.Table, (∀ p ∈ reads, x p = y p) → ∀ p ∈ writes, update x p = update y p

namespace ProcessProfile

variable {A : Presentation}

open Classical in
/-- Making the change: the write footprint takes the proposed values, and
every other position keeps its value. -/
noncomputable def apply (u : ProcessProfile A) (x : A.Table) : A.Table :=
  fun p => if p ∈ u.writes then u.update x p else x p

end ProcessProfile

/-- **Definition 2.5** (enabled application). The evidence that the guard of a
profile holds at the table `x`, together with its proposal. -/
@[book "def:process-profile"]
structure EnabledApp (A : Presentation) (x : A.Table) where
  /-- The profile applied. -/
  profile : ProcessProfile A
  /-- Its guard holds at `x`. -/
  enabled : profile.guard x

namespace EnabledApp

variable {A : Presentation} {x : A.Table}

/-- **Definition 2.6** (compatibility). Two enabled applications are
compatible when their writes do not conflict, their write footprints being
disjoint, and neither write invalidates a value that the other proposal
assumed: making one leaves every position the other reads unchanged. -/
@[book "def:batch"]
def Compatible (a b : EnabledApp A x) : Prop :=
  Disjoint a.profile.writes b.profile.writes ∧
  (∀ p ∈ b.profile.reads, a.profile.apply x p = x p) ∧
  (∀ p ∈ a.profile.reads, b.profile.apply x p = x p)

end EnabledApp

/-- **Definition 2.6** (batch). A finite family of pairwise compatible
enabled applications, together with the evidence of their compatibility. -/
@[book "def:batch"]
structure Batch (A : Presentation) (x : A.Table) where
  /-- The applications, listed in one order. -/
  apps : List (EnabledApp A x)
  /-- They are pairwise compatible. -/
  compatible : apps.Pairwise EnabledApp.Compatible

/-- Making a list of changes one after another, in the order listed. -/
noncomputable def applyAll {A : Presentation} {x : A.Table} :
    List (EnabledApp A x) → A.Table → A.Table
  | [], y => y
  | a :: l, y => applyAll l (a.profile.apply y)

/-- The state a batch leads to, its changes made in the order listed. -/
noncomputable def Batch.apply {A : Presentation} {x : A.Table} (b : Batch A x) : A.Table :=
  applyAll b.apps x

end Artform
