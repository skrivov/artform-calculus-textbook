import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import ArtformTextbook.Ch01.Defs.Forms

/-!
# Artform frames and instances (*Constructing a space and its states*)

Definition 1.13: an artform frame is a typed specification of a carrier, its
carried structure, the space of legal states, the allowed observations and the
allowed moves; an artform instance is one legal state inhabiting the frame.

* `ArtformFrame`: the carrier with its carried structure is a finite form
  (Definition 1.1). The space of legal states is given by the states the frame
  describes and the condition that makes one legal. An observation reads a
  value from a state. A move relates a state to the states it may lead to, and
  leads from legal states to legal states.
* `ArtformFrame.Instance`: a legal state.

Legality is a proposition: an instance is a state together with the fact that
it is legal, so two instances with the same state are equal. This is how the
book counts states, through their values.
-/

namespace Artform

/-- **Definition 1.13** (artform frame). A typed specification of a carrier and
its carried structure, a finite form of a declared type; the space of legal
states, given by the states and their legality; the allowed observations, each
reading a value from a state; and the allowed moves, each relating a state to
the states it may lead to, from legal states to legal states. -/
@[book "def:frame-instance"]
structure ArtformFrame where
  /-- The type of the carrier: the carried structure it declares. -/
  carrierType : FormType
  /-- The carrier with its carried structure. -/
  carrier : FiniteForm carrierType
  /-- The states the frame describes. -/
  State : Type
  /-- The legal states. -/
  Legal : State → Prop
  /-- The allowed observations. -/
  Obs : Type
  /-- The values each observation reads. -/
  Value : Obs → Type
  /-- Reading an observation at a state. -/
  read : (o : Obs) → State → Value o
  /-- The allowed moves. -/
  Move : Type
  /-- `step m x y`: the move `m` may lead from `x` to `y`. -/
  step : Move → State → State → Prop
  /-- A move leads from a legal state to a legal state. -/
  step_legal : ∀ m x y, step m x y → Legal x → Legal y

/-- **Definition 1.13** (artform instance): one legal state inhabiting the
frame. -/
@[book "def:frame-instance"]
def ArtformFrame.Instance (F : ArtformFrame) : Type := {x : F.State // F.Legal x}

/-! ## Non-vacuity -/

/-- One token on three cells in a row: the carrier is the row with its order,
a state puts `true` or `false` on each cell, a state is legal when exactly one
cell holds `true`, an observation reads one cell, and the one move passes the
token to the next cell, from the last back to the first. -/
abbrev tokenFrame : ArtformFrame where
  carrierType := relationFormType
  carrier := ⟨Fin 3, fun i j => i < j⟩
  State := Fin 3 → Bool
  Legal x := (Finset.univ.filter fun i => x i = true).card = 1
  Obs := Fin 3
  Value _ := Bool
  read i x := x i
  Move := Unit
  step _ x y := y = fun i => x (i - 1)
  step_legal _ x y h hx := by
    subst h
    revert hx
    revert x
    decide

/-- The state with the token on the first cell is an instance. -/
example : tokenFrame.Instance := ⟨fun i => decide (i = 0), by decide⟩

end Artform
