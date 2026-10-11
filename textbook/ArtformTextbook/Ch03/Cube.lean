import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic.FinCases
import ArtformTextbook.Ch03.Statements.Cube

/-!
# The cube boundary assembled from squares (Proposition 3.4)

The book's proof: the classes of joined cells are exactly the triples with at most two stars, and
incidence specializes a star in the pieces and in the target alike, so the joined canvas is the
cube boundary; the remaining address `(*, *, *)` is one new three-cell whose immediate faces are
the six coordinate faces. The counts `(8, 12, 6, 1)` are then read off the descriptor.
-/

namespace Artform

open IncidenceCanvas

theorem Tri.exists_ofBool {t : Tri} (h : t ≠ Tri.star) : ∃ b, Tri.ofBool b = t := by
  cases t
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩
  · exact absurd rfl h

/-- Isomorphic canvases have the same number of cells in each dimension. -/
theorem IncidenceCanvas.Iso.cellCount_eq {X Y : IncidenceCanvas} (e : X.Iso Y) (k : ℕ) :
    X.cellCount k = Y.cellCount k :=
  Finset.card_equiv e.toEquiv fun c => by simp [e.dim_eq]

/-- The three-cell `(*, *, *)` has exactly the cells of dimension two as immediate faces. -/
theorem cube_face_top_iff (c : Fin 3 → Tri) :
    cubeCanvas.Face c (fun _ => Tri.star) ↔ cubeCanvas.dim c = 2 := by
  revert c
  decide

theorem cube_not_face_top (d : Fin 3 → Tri) : ¬ cubeCanvas.Face (fun _ => Tri.star) d := by
  rintro ⟨i, -, h, -⟩
  exact h rfl

/-- Attaching a three-cell along the whole boundary of an instance of the cube boundary gives an
instance of the cube, the new cell going to `(*, *, *)`. -/
def attachTopIso (X : IncidenceCanvas) (e : X.Iso cubeBoundaryCanvas) :
    (X.attachTop 2).Iso cubeCanvas where
  toEquiv := (Equiv.optionCongr e.toEquiv).trans (Equiv.optionSubtypeNe fun _ => Tri.star)
  dim_eq a := by
    cases a with
    | none =>
      change cubeCanvas.dim (fun _ => Tri.star) = 2 + 1
      decide
    | some P => exact e.dim_eq P
  face_iff a b := by
    cases a with
    | none => exact iff_of_false (cube_not_face_top _) fun h => (h : False)
    | some P =>
      cases b with
      | none =>
        change cubeCanvas.Face (e.toEquiv P).1 (fun _ => Tri.star) ↔ X.dim P = 2
        rw [cube_face_top_iff, show cubeCanvas.dim (e.toEquiv P).1 = X.dim P from e.dim_eq P]
      | some Q => exact e.face_iff P Q

namespace CubeAssembly

variable (S : CoordFace → IncidenceCanvas) (χ : ∀ f, (S f).Iso (faceClosure f))

theorem address_mem (p : Σ f, (S f).Cell) : address S χ p p.1.1 = Tri.ofBool p.1.2 :=
  ((χ p.1).toEquiv p.2).2

theorem address_ne_top (p : Σ f, (S f).Cell) : address S χ p ≠ fun _ => Tri.star := by
  intro h
  have h1 := address_mem S χ p
  rw [h] at h1
  rcases p with ⟨⟨i, b⟩, x⟩
  cases b <;> simp [Tri.ofBool] at h1

/-- A joined cell goes to its address, a cell of the cube boundary. -/
def toBoundary : (assemble S χ).Cell → cubeBoundaryCanvas.Cell :=
  Quotient.lift (s := setoid S χ) (fun p => ⟨address S χ p, address_ne_top S χ p⟩)
    fun _ _ h => Subtype.ext h

theorem toBoundary_injective : Function.Injective (toBoundary S χ) := by
  intro P Q h
  obtain ⟨p, rfl⟩ := Quotient.exists_rep (s := setoid S χ) P
  obtain ⟨q, rfl⟩ := Quotient.exists_rep (s := setoid S χ) Q
  exact Quotient.sound (congrArg Subtype.val h)

/-- Every triple with at most two stars is the address of a cell of some piece: a coordinate
that is not a star names a face whose closure holds it. -/
theorem toBoundary_surjective : Function.Surjective (toBoundary S χ) := by
  rintro ⟨c, hc⟩
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ Tri.star := by
    by_contra h
    exact hc (funext fun j => Classical.byContradiction fun hj => h ⟨j, hj⟩)
  obtain ⟨b, hb⟩ := Tri.exists_ofBool hi
  let y : (faceClosure (i, b)).Cell := ⟨c, hb.symm⟩
  refine ⟨Quotient.mk (setoid S χ) ⟨(i, b), (χ (i, b)).toEquiv.symm y⟩, Subtype.ext ?_⟩
  change address S χ ⟨(i, b), (χ (i, b)).toEquiv.symm y⟩ = c
  exact congrArg Subtype.val ((χ (i, b)).toEquiv.apply_symm_apply y)

/-- The joined canvas is an instance of the cube boundary. -/
noncomputable def boundaryIso : (assemble S χ).Iso cubeBoundaryCanvas where
  toEquiv := Equiv.ofBijective _ ⟨toBoundary_injective S χ, toBoundary_surjective S χ⟩
  dim_eq P := by
    obtain ⟨p, rfl⟩ := Quotient.exists_rep (s := setoid S χ) P
    exact (dim_eq_address S χ p).symm
  face_iff P Q := by
    obtain ⟨p, rfl⟩ := Quotient.exists_rep (s := setoid S χ) P
    obtain ⟨q, rfl⟩ := Quotient.exists_rep (s := setoid S χ) Q
    change cubeCanvas.Face (address S χ p) (address S χ q) ↔ _
    constructor
    · intro hf
      rcases q with ⟨⟨i, b⟩, y⟩
      obtain ⟨k, hk, -, hpq⟩ := id hf
      have hq : address S χ ⟨(i, b), y⟩ i = Tri.ofBool b := address_mem S χ ⟨(i, b), y⟩
      have hik : i ≠ k := by
        rintro rfl
        rw [hk] at hq
        cases b <;> simp [Tri.ofBool] at hq
      have hpi : address S χ p i = Tri.ofBool b := (hpq i hik).trans hq
      let z : (faceClosure (i, b)).Cell := ⟨address S χ p, hpi⟩
      refine ⟨(i, b), (χ (i, b)).toEquiv.symm z, y,
        Quotient.sound (congrArg Subtype.val ((χ (i, b)).toEquiv.apply_symm_apply z)).symm, rfl,
        ?_⟩
      rw [← (χ (i, b)).face_iff, Equiv.apply_symm_apply]
      exact hf
    · rintro ⟨f, x, y, hP, hQ, hxy⟩
      have e1 : address S χ p = address S χ ⟨f, x⟩ := Quotient.exact hP
      have e2 : address S χ q = address S χ ⟨f, y⟩ := Quotient.exact hQ
      rw [e1, e2]
      exact ((χ f).face_iff x y).mpr hxy

end CubeAssembly

/-- **Proposition 3.4** (cube boundary assembled from squares). The six squares joined along
their charts form an instance of the cube boundary; with the three-cell attached they form an
instance of the cube, with `8` vertices, `12` edges, `6` faces and `1` three-cell. -/
@[book "prop:cube-assembly-book"]
theorem cubeAssembly : Statement.cubeAssembly := by
  intro S _ χ
  have e := CubeAssembly.boundaryIso S χ
  have e' := attachTopIso _ e
  refine ⟨⟨e⟩, ⟨e'⟩, ?_, ?_, ?_, ?_⟩ <;> rw [e'.cellCount_eq] <;> decide

/-! ## Non-vacuity -/

/-- The closure of a coordinate face, read through its two free coordinates. -/
def faceSquareEquiv (f : CoordFace) : (faceClosure f).Cell ≃ squareCanvas.Cell where
  toFun c := Fin.removeNth f.1 c.1
  invFun p := ⟨Fin.insertNth f.1 (Tri.ofBool f.2) p, Fin.insertNth_apply_same _ _ _⟩
  left_inv c := by
    have hc : c.1 f.1 = Tri.ofBool f.2 := c.2
    apply Subtype.ext
    change Fin.insertNth f.1 (Tri.ofBool f.2) (Fin.removeNth f.1 c.1) = c.1
    exact (congrArg (fun t => Fin.insertNth f.1 t (Fin.removeNth f.1 c.1)) hc.symm).trans
      (Fin.insertNth_self_removeNth _ _)
  right_inv p := Fin.removeNth_insertNth _ _ _

/-- Each face closure of the cube is a square (Section 3.2). -/
theorem faceClosure_isInstance (f : CoordFace) : (faceClosure f).IsInstance squareCanvas := by
  rcases f with ⟨i, b⟩
  fin_cases i <;> cases b <;>
    exact ⟨{
      toEquiv := faceSquareEquiv _
      dim_eq := by decide
      face_iff := by
        intro a b
        change squareCanvas.Face (Fin.removeNth _ a.1) (Fin.removeNth _ b.1) ↔
          cubeCanvas.Face a.1 b.1
        revert a b
        decide }⟩

/-- Proposition 3.4: the six face closures of the cube, each with the identity as its chart, are
six square instances with the coordinate-face gluing data. -/
example : (∀ f, (faceClosure f).IsInstance squareCanvas) ∧
    ∀ f, Nonempty ((faceClosure f).Iso (faceClosure f)) :=
  ⟨faceClosure_isInstance, fun _ => ⟨Iso.refl _⟩⟩

end Artform
