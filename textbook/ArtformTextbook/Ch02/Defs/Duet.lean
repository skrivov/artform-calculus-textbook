import Mathlib.Data.ZMod.Defs
import ArtformTextbook.Ch01.Defs.Frames
import ArtformTextbook.Ch06.Defs.Window

/-!
# The stage and the legal duet states (*A stage of squares*; *Dancers and their moves*)

* Definition 2.1: the stage `K_n`, `n ≥ 2`. Its places are the centre `o`,
  the orbit sites `v_i` and the gates `g_i`, indices modulo `2n`. It declares
  three incidences: a spoke from every orbit site to the centre, a gate edge
  from each orbit site to its gate, and the ring `v_i → v_{i+1}`, with its
  orientation. The stage `K_2` is `SquareGrid(5, 5)` with the palette that names
  nine faces (`Stage.face`); the grid realizes the three incidences
  (`Stage.marking`).
* The root places `R_n` are the orbit sites and the gates. A placement puts
  the two dancers' roots on root places, no two on one; with placements as its
  states the stage is a frame in the sense of Definition 1.13
  (`Stage.frame`).
* Definition 2.2: a candidate state `x = (ℓ, f, γ, κ)` and its legality,
  conditions (A1)–(A4), for a declared gesture alphabet and mirror relation.
  The duet's alphabet and mirror relation are `duetAlphabet` and `duetMirror`.

A facing is recorded as the index of the place faced: by (A2) a dancer at a
place of index `i` faces index `i + n`, across the centre.
-/

namespace Artform

namespace Duet

/-- The places of the stage `K_n` (Definition 2.1): the centre `o`, the orbit
sites `v_i` and the gates `g_i`, with `i` taken modulo `2n`. -/
inductive Place (n : ℕ) where
  /-- The centre `o`. -/
  | centre
  /-- The orbit site `v_i`. -/
  | orbit (i : ZMod (2 * n))
  /-- The gate `g_i`. -/
  | gate (i : ZMod (2 * n))
  deriving DecidableEq

namespace Place

variable {n : ℕ}

/-- **Definition 2.1** (stage frame): the spokes, one from every orbit site to
the centre. -/
@[book "def:stage"]
def Spoke : Place n → Place n → Prop
  | orbit _, centre => True
  | _, _ => False

/-- **Definition 2.1** (stage frame): the gate edges, one from each orbit site
to its gate. -/
@[book "def:stage"]
def GateEdge : Place n → Place n → Prop
  | orbit i, gate j => i = j
  | _, _ => False

/-- **Definition 2.1** (stage frame): the ring of orbit sites, with its
orientation `v_i → v_{i+1}`. -/
@[book "def:stage"]
def Ring : Place n → Place n → Prop
  | orbit i, orbit j => j = i + 1
  | _, _ => False

instance : DecidableRel (Spoke : Place n → Place n → Prop) := fun p q => by
  cases p <;> cases q <;> unfold Spoke <;> infer_instance

instance : DecidableRel (GateEdge : Place n → Place n → Prop) := fun p q => by
  cases p <;> cases q <;> unfold GateEdge <;> infer_instance

instance : DecidableRel (Ring : Place n → Place n → Prop) := fun p q => by
  cases p <;> cases q <;> unfold Ring <;> infer_instance

/-- The root places `R_n = {v_i, g_i}`: the orbit sites and the gates. The
centre is not among them. -/
def IsRoot : Place n → Prop
  | centre => False
  | _ => True

instance : DecidablePred (IsRoot : Place n → Prop) := fun p => by
  cases p <;> unfold IsRoot <;> infer_instance

/-- The index `i` of a root place `v_i` or `g_i`; the centre is given `0`,
which no condition uses. -/
def index : Place n → ZMod (2 * n)
  | centre => 0
  | orbit i => i
  | gate i => i

end Place

/-- The two dancers, `A` and `B`. -/
inductive Dancer where
  | A
  | B
  deriving DecidableEq

/-- The places of `K_2`, listed: the centre, the four orbit sites and the four
gates. -/
instance : Fintype (Place 2) :=
  Fintype.ofEquiv (Unit ⊕ ZMod 4 ⊕ ZMod 4)
    { toFun := fun
        | .inl _ => .centre
        | .inr (.inl i) => .orbit i
        | .inr (.inr i) => .gate i
      invFun := fun
        | .centre => .inl ()
        | .orbit i => .inr (.inl i)
        | .gate i => .inr (.inr i)
      left_inv := by rintro (_ | _ | _) <;> rfl
      right_inv := by rintro (_ | _ | _) <;> rfl }

/-! ## Definition 2.1: the stage -/

/-- **Definition 2.1** (stage frame). The stage `K_n`, for `n ≥ 2`: its places,
a centre, `2n` orbit sites `v₀, …, v_{2n-1}` and a gate on each orbit site;
and its incidences, a spoke from every orbit site to the centre, a gate edge
from each orbit site to its gate, and the ring with the orientation
`v_i → v_{i+1}`, indices modulo `2n` (`Place.Spoke`, `Place.GateEdge`,
`Place.Ring`). -/
@[book "def:stage"]
structure Stage where
  /-- The number `n`: the stage has `2n` orbit sites. -/
  n : ℕ
  /-- `n ≥ 2`. -/
  two_le : 2 ≤ n

namespace Stage

/-- The places of the stage. -/
abbrev Places (K : Stage) : Type := Place K.n

/-- The stage `K_2`. -/
def two : Stage := ⟨2, le_rfl⟩

/-- **Definition 2.1** (stage frame, `K_2`): the palette that names nine faces
of `SquareGrid(5, 5)`, given as the face of each place. The centre is the
central face `(2, 2)`; the orbit sites are the four faces that share an edge
with it, `v₀` to the west and then anticlockwise; each gate is the face beyond
its orbit site. -/
@[book "def:stage"]
def face : Place 2 → GridFace 5 5
  | .centre => (2, 2)
  | .orbit i => ![(1, 2), (2, 1), (3, 2), (2, 3)] i
  | .gate i => ![(0, 2), (2, 0), (4, 2), (2, 4)] i

/-- Two faces of a square grid share an edge: their coordinates differ by one
in one place. -/
def ShareEdge {m n : ℕ} (f f' : GridFace m n) : Prop :=
  (f.1 = f'.1 ∧ (f.2.val + 1 = f'.2.val ∨ f'.2.val + 1 = f.2.val)) ∨
    (f.2 = f'.2 ∧ (f.1.val + 1 = f'.1.val ∨ f'.1.val + 1 = f.1.val))

/-- Two faces of a square grid share a corner and no edge: their coordinates
differ by one in both places. -/
def ShareCorner {m n : ℕ} (f f' : GridFace m n) : Prop :=
  (f.1.val + 1 = f'.1.val ∨ f'.1.val + 1 = f.1.val) ∧
    (f.2.val + 1 = f'.2.val ∨ f'.2.val + 1 = f.2.val)

instance {m n : ℕ} : DecidableRel (ShareEdge : GridFace m n → GridFace m n → Prop) :=
  fun _ _ => by unfold ShareEdge; infer_instance

instance {m n : ℕ} : DecidableRel (ShareCorner : GridFace m n → GridFace m n → Prop) :=
  fun _ _ => by unfold ShareCorner; infer_instance

/-- `K_2` is a marking of `SquareGrid(5, 5)`: the palette names nine distinct
faces, a spoke and a gate edge join faces that share an edge, and the ring
joins faces that share a corner. -/
theorem marking :
    Function.Injective face ∧
    (∀ i : ZMod 4, ShareEdge (face (.orbit i)) (face .centre)) ∧
    (∀ i : ZMod 4, ShareEdge (face (.orbit i)) (face (.gate i))) ∧
    (∀ i : ZMod 4, ShareCorner (face (.orbit i)) (face (.orbit (i + 1)))) := by
  decide

/-! ## Placements, and the stage as a frame -/

/-- A placement on the stage `K`: each dancer's root on a root place, no two on
one place. -/
def Placement (K : Stage) : Type :=
  {ℓ : Dancer → K.Places // Function.Injective ℓ ∧ ∀ d, (ℓ d).IsRoot}

/-- The stage as a frame (Definition 1.13): the carrier is the stage, its places
with the three incidences; the states are the assignments of places to the
dancers, legal when they are placements; an observation reads one dancer's
place; the stage declares no move, since it does not move while the dancers
do. -/
def frame (K : Stage) [Fintype K.Places] : ArtformFrame where
  carrierType := ⟨fun C => (C → C → Prop) × (C → C → Prop) × (C → C → Prop)⟩
  carrier := ⟨K.Places, (Place.Spoke, Place.GateEdge, Place.Ring)⟩
  State := Dancer → K.Places
  Legal ℓ := Function.Injective ℓ ∧ ∀ d, (ℓ d).IsRoot
  Obs := Dancer
  Value _ := K.Places
  read d ℓ := ℓ d
  Move := Empty
  step m _ _ := m.elim
  step_legal m := m.elim

end Stage

/-! ## Definition 2.2: legal duet states -/

/-- A hand. -/
inductive Hand where
  | left
  | right
  deriving DecidableEq

/-- A candidate state `x = (ℓ, f, γ, κ)` on the stage `K_n`, with gestures of
type `G` (Definition 2.2): the placement `ℓ` of the dancers' roots, the facing
`f` of each dancer, given as the index of the place it faces, the gesture `γ`
of each dancer, and a contact record `κ`, which may be absent and names a hand
of `A`, a hand of `B` and a place. -/
structure CandidateState (n : ℕ) (G : Type) where
  /-- The placement `ℓ`. -/
  ℓ : Dancer → Place n
  /-- The facing `f`: the index of the place each dancer faces. -/
  f : Dancer → ZMod (2 * n)
  /-- The gesture `γ` of each dancer. -/
  γ : Dancer → G
  /-- The contact record `κ`, if present: a hand of `A`, a hand of `B`, a
  place. -/
  κ : Option (Hand × Hand × Place n)

/-- **Definition 2.2** (legal duet state). For a declared gesture alphabet and
mirror relation, a candidate state `x = (ℓ, f, γ, κ)` on `K_n` is legal when
* (A1) both roots lie in `R_n`, and `ℓ(A) ≠ ℓ(B)`;
* (A2) a dancer at a place of index `i` faces the place of index `i + n`,
  across the centre;
* (A3) each gesture lies in the alphabet, and the pair `(γ(A), γ(B))` lies in
  the mirror relation;
* (A4) if `κ` is present, both roots are orbit sites `v_i` and `v_j` with
  `j - i = n` modulo `2n`, and `κ` names one hand of each dancer and the
  centre `o`. -/
@[book "def:legal-state"]
def CandidateState.Legal {n : ℕ} {G : Type} (alphabet : Set G) (mirror : G → G → Prop)
    (x : CandidateState n G) : Prop :=
  ((x.ℓ .A).IsRoot ∧ (x.ℓ .B).IsRoot ∧ x.ℓ .A ≠ x.ℓ .B) ∧
  (∀ d, x.f d = (x.ℓ d).index + n) ∧
  (x.γ .A ∈ alphabet ∧ x.γ .B ∈ alphabet ∧ mirror (x.γ .A) (x.γ .B)) ∧
  (∀ c ∈ x.κ, (∃ i j : ZMod (2 * n), x.ℓ .A = .orbit i ∧ x.ℓ .B = .orbit j ∧ j - i = n) ∧
    c.2.2 = .centre)

/-- The gestures of the duet's eight-count phrase. -/
inductive Gesture where
  | approach
  | extendRight
  | extendLeft
  | offerRight
  | receiveLeft
  | hold
  | orbit
  | releaseRight
  | releaseLeft
  | resolve
  deriving DecidableEq

/-- The duet's gesture alphabet: every gesture of the phrase. -/
def duetAlphabet : Set Gesture := Set.univ

/-- The duet's mirror relation: extend right with extend left, offer right with
receive left, release right with release left, and each other gesture with
itself. -/
def duetMirror : Gesture → Gesture → Prop
  | .extendRight, g => g = .extendLeft
  | .offerRight, g => g = .receiveLeft
  | .releaseRight, g => g = .releaseLeft
  | .extendLeft, _ => False
  | .receiveLeft, _ => False
  | .releaseLeft, _ => False
  | g, g' => g' = g

/-! ## Non-vacuity -/

/-- The opening state on `K_2`: `A` at the gate `g₀` and `B` at the gate `g₂`,
facing across the centre, both holding, without contact. It is legal. -/
example : CandidateState.Legal duetAlphabet duetMirror
    (⟨fun d => match d with | .A => .gate 0 | .B => .gate 2,
      fun d => match d with | .A => 2 | .B => 0,
      fun _ => .hold, none⟩ : CandidateState 2 Gesture) := by
  refine ⟨⟨trivial, trivial, by decide⟩, fun d => ?_, ⟨trivial, trivial, rfl⟩, fun c hc => ?_⟩
  · cases d <;> decide
  · cases hc

end Duet

end Artform
