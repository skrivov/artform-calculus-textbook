import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import ArtformTextbook.Ch03.Defs.Canvas

/-!
# Six squares make the cube boundary (Section 3.2)

`Canvas` (Definition 3.1 in dimension two, with its stored orientation) cannot hold a three-cell.
This file states Definition 3.1 in any dimension, without orientation, as `IncidenceCanvas`:
finitely many cells, each with its dimension, and the immediate-face relation, which raises
dimension by exactly one. A two-dimensional `Canvas` gives one by forgetting its orientation
(`Canvas.toIncidenceCanvas`).

The cubical descriptor of Section 3.2 has the addresses `{0, 1, *}³` as its cells: the number of
stars is the dimension, and replacing one star by `0` or `1` gives an immediate face. The same
construction on `{0, 1, *}²` is the square. Instances of a descriptor are compared by structural
isomorphisms: bijections of cells keeping dimension and immediate incidence in both directions.
-/

namespace Artform

/-- **Definition 3.1** (finite cellular canvas), in any dimension and without orientation: the
graded cells `C_k(X)`, given as one finite set of cells with the dimension of each, and the
immediate-face relation `a ⋖ b`, which raises dimension by exactly one. The outer boundary `∂X`
is not part of this structure: the structural comparisons of Section 3.2 exclude it. The local
boundary data are not stored either: for the unoriented polygonal faces used here (squares), the
boundary cycle of a face, up to rotation and reversal, is determined by incidence. -/
@[book "def:canvas"]
structure IncidenceCanvas where
  /-- The cells. -/
  Cell : Type
  [fintypeCell : Fintype Cell]
  [decEqCell : DecidableEq Cell]
  /-- The dimension of each cell. -/
  dim : Cell → ℕ
  /-- The immediate-face relation: `Face a b` is `a ⋖ b`. -/
  Face : Cell → Cell → Prop
  /-- An immediate face is one dimension lower. -/
  face_dim : ∀ a b, Face a b → dim b = dim a + 1

attribute [instance] IncidenceCanvas.fintypeCell IncidenceCanvas.decEqCell

namespace IncidenceCanvas

/-- A structural isomorphism (Section 3.2): a bijection of cells that keeps the dimension and the
immediate-face relation in both directions. -/
structure Iso (X Y : IncidenceCanvas) where
  /-- The bijection of cells. -/
  toEquiv : X.Cell ≃ Y.Cell
  dim_eq : ∀ a, Y.dim (toEquiv a) = X.dim a
  face_iff : ∀ a b, Y.Face (toEquiv a) (toEquiv b) ↔ X.Face a b

/-- The identity structural isomorphism. -/
def Iso.refl (X : IncidenceCanvas) : X.Iso X where
  toEquiv := Equiv.refl _
  dim_eq _ := rfl
  face_iff _ _ := Iff.rfl

/-- **Definition 1.12** (geometric form and its instances), for the geometric profile that
retains grading and immediate incidence, which is the profile of Section 3.2. A geometric form is
given by its representative canvas `P`; a canvas `X` is an instance when its cells can be put in
bijection with those of `P`, preserving the selected structure in both directions. -/
@[book "def:geometric-form-book"]
def IsInstance (X P : IncidenceCanvas) : Prop := Nonempty (X.Iso P)

/-- The number of cells of dimension `k`. -/
def cellCount (X : IncidenceCanvas) (k : ℕ) : ℕ := (Finset.univ.filter fun c => X.dim c = k).card

/-- The subcanvas on the cells satisfying `p`, with the induced dimension and incidence. -/
def sub (X : IncidenceCanvas) (p : X.Cell → Prop) [DecidablePred p] : IncidenceCanvas where
  Cell := {c // p c}
  dim c := X.dim c
  Face a b := X.Face a b
  face_dim a b h := X.face_dim a b h

/-- Adding one cell of dimension `n + 1` along the whole `n`-dimensional part: its immediate faces
are all the cells of dimension `n`. -/
def attachTop (X : IncidenceCanvas) (n : ℕ) : IncidenceCanvas where
  Cell := Option X.Cell
  dim
    | none => n + 1
    | some c => X.dim c
  Face
    | some a, some b => X.Face a b
    | some a, none => X.dim a = n
    | none, _ => False
  face_dim a b h := by
    match a, b, h with
    | some a, some b, h => exact X.face_dim a b h
    | some _, none, h => exact congrArg (· + 1) h.symm

end IncidenceCanvas

/-- The two-dimensional canvas of `Canvas.lean` as an incidence canvas: its vertices, edges and
faces, of dimensions `0`, `1` and `2`, with the endpoints of each edge and the edges of each
face's boundary cycle as immediate faces. The orientation is forgotten. -/
def Canvas.toIncidenceCanvas (K : Canvas) : IncidenceCanvas where
  Cell := K.V ⊕ K.E ⊕ K.F
  dim
    | .inl _ => 0
    | .inr (.inl _) => 1
    | .inr (.inr _) => 2
  Face
    | .inl v, .inr (.inl e) => v = K.src e ∨ v = K.tgt e
    | .inr (.inl e), .inr (.inr f) => e ∈ (K.boundary f).map Prod.fst
    | _, _ => False
  face_dim a b h := by
    rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> first | rfl | exact h.elim

/-! ## The cubical descriptor -/

/-- A coordinate of a cubical address: `0`, `1`, or a star `*` (free). -/
inductive Tri where
  | zero
  | one
  | star
  deriving DecidableEq

instance : Fintype Tri := Fintype.ofList [.zero, .one, .star] fun t => by cases t <;> simp

/-- The coordinate value `0` (`false`) or `1` (`true`). -/
def Tri.ofBool : Bool → Tri
  | false => .zero
  | true => .one

/-- The cubical descriptor in dimension `n`: the cells are the addresses in `{0, 1, *}ⁿ`, the
number of stars is the dimension, and replacing one star by `0` or `1` gives an immediate
face. -/
@[reducible] def boxCanvas (n : ℕ) : IncidenceCanvas where
  Cell := Fin n → Tri
  dim c := (Finset.univ.filter fun i => c i = Tri.star).card
  Face a b := ∃ i, b i = Tri.star ∧ a i ≠ Tri.star ∧ ∀ j, j ≠ i → a j = b j
  face_dim := by
    rintro a b ⟨i, hb, ha, hab⟩
    have h : (Finset.univ.filter fun j => b j = Tri.star) =
        insert i (Finset.univ.filter fun j => a j = Tri.star) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp [hb]
      · simp [hj, hab j hj]
    rw [h, Finset.card_insert_of_notMem (by simp [ha])]

/-- The square descriptor: four vertices, four edges and one face, as the addresses
`{0, 1, *}²`. -/
abbrev squareCanvas : IncidenceCanvas := boxCanvas 2

/-- The filled cubical descriptor, with its three-cell `(*, *, *)`. -/
abbrev cubeCanvas : IncidenceCanvas := boxCanvas 3

/-- The cube-boundary descriptor: the cubical descriptor without the three-cell `(*, *, *)`. -/
def cubeBoundaryCanvas : IncidenceCanvas := cubeCanvas.sub fun c => c ≠ fun _ => Tri.star

/-- The six coordinate faces of the cube: a coordinate, and the value `0` (`false`) or
`1` (`true`) at which it is fixed. -/
abbrev CoordFace : Type := Fin 3 × Bool

/-- The closure of a coordinate face in the cubical descriptor: the cells whose address has the
fixed coordinate at its value. Its two remaining coordinates range over `{0, 1, *}`. -/
def faceClosure (f : CoordFace) : IncidenceCanvas :=
  cubeCanvas.sub fun c => c f.1 = Tri.ofBool f.2

/-! ## Joining six squares along their addresses -/

namespace CubeAssembly

variable (S : CoordFace → IncidenceCanvas) (χ : ∀ f, (S f).Iso (faceClosure f))

/-- The triple address that the chart of a piece gives one of its cells. -/
def address (p : Σ f, (S f).Cell) : Fin 3 → Tri := ((χ p.1).toEquiv p.2).1

/-- Two cells of the pieces are joined when their addresses agree. -/
def setoid : Setoid (Σ f, (S f).Cell) where
  r p q := address S χ p = address S χ q
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- A cell has the dimension of its address. -/
theorem dim_eq_address (p : Σ f, (S f).Cell) :
    (S p.1).dim p.2 = cubeCanvas.dim (address S χ p) :=
  ((χ p.1).dim_eq p.2).symm

/-- The canvas joined from six squares with charts (Section 3.2): its cells are the cells of the
pieces, two of them being identified exactly when their charts give them the same triple; the
dimension and the incidence come from the pieces. -/
def assemble : IncidenceCanvas where
  Cell := Quotient (setoid S χ)
  fintypeCell := @Quotient.fintype _ _ (setoid S χ) fun p q =>
    (inferInstance : Decidable (address S χ p = address S χ q))
  decEqCell := @Quotient.decidableEq _ (setoid S χ) fun p q =>
    (inferInstance : Decidable (address S χ p = address S χ q))
  dim := Quotient.lift (fun p => (S p.1).dim p.2) fun p q (h : address S χ p = address S χ q) => by
    rw [dim_eq_address, dim_eq_address, h]
  Face P Q := ∃ (f : CoordFace) (x y : (S f).Cell),
    P = Quotient.mk _ ⟨f, x⟩ ∧ Q = Quotient.mk _ ⟨f, y⟩ ∧ (S f).Face x y
  face_dim := by
    rintro _ _ ⟨f, x, y, rfl, rfl, h⟩
    exact (S f).face_dim x y h

end CubeAssembly

end Artform
