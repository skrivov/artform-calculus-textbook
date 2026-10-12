import Mathlib.Data.Fintype.Basic
import ArtformTextbook.Meta.Book

/-!
# Finite forms (*Building finite forms*)

Definition 1.1: a finite form is a finite set of cells together with the
carried structure that its type declares.

* `FormType`: a type of forms. It declares which carried structure is
  relevant: for a set of cells, the type of the structure that a form of this
  type holds on them.
* `FiniteForm τ`: a finite form of type `τ`, a finite cell set with carried
  structure of the kind `τ` declares.
* `FiniteForm.eq_iff`: two forms of one type are identical exactly when their
  cells and their declared data agree. Data that the type does not declare are
  not part of a form, so they cannot tell two forms apart.
-/

namespace Artform

/-- **Definition 1.1** (finite form): a type of forms. It declares which
carried structure is relevant: for a set of cells `C`, `Carried C` is the type
of the structure that a form of this type holds on `C`. Types, tags, orders,
incidence relations, orientations, labels and distinguished cells are carried
structure of this kind. -/
@[book "def:finite-form"]
structure FormType where
  /-- The carried structure on the cells `C`. -/
  Carried : Type → Type

/-- **Definition 1.1** (finite form). A finite form `X` of type `τ`: a finite
cell set `cells(X)` together with carried structure of the kind `τ`
declares. -/
@[book "def:finite-form"]
structure FiniteForm (τ : FormType) where
  /-- The cells, `cells(X)`. -/
  cells : Type
  /-- There are finitely many cells. -/
  [fintype : Fintype cells]
  /-- The declared carried structure. -/
  carried : τ.Carried cells

attribute [instance] FiniteForm.fintype

namespace FiniteForm

variable {τ : FormType}

/-- Two forms of one type are identical exactly when they have the same cells
and the same declared data (Definition 1.1). -/
theorem eq_iff (X Y : FiniteForm τ) :
    X = Y ↔ X.cells = Y.cells ∧ HEq X.carried Y.carried := by
  constructor
  · rintro rfl
    exact ⟨rfl, HEq.rfl⟩
  · cases X with
    | mk C s =>
      cases Y with
      | mk D t =>
        rintro ⟨h, hst⟩
        dsimp only at h hst
        subst h
        cases eq_of_heq hst
        congr 1
        exact Subsingleton.elim _ _

end FiniteForm

/-- The forms whose carried structure is one relation on the cells, such as an
order or an incidence relation. -/
def relationFormType : FormType := ⟨fun C => C → C → Prop⟩

/-! ## Non-vacuity -/

/-- Three cells in a row, with their order, as a form whose type declares one
relation. -/
example : FiniteForm relationFormType := ⟨Fin 3, fun i j => i < j⟩

/-- The order is declared, so two forms on the same cells with different orders
are different forms. -/
example : (⟨Fin 3, fun i j => i < j⟩ : FiniteForm relationFormType) ≠
    ⟨Fin 3, fun i j => j < i⟩ := by
  intro h
  have := congrFun (congrFun (eq_of_heq ((FiniteForm.eq_iff _ _).mp h).2) 0) 1
  simp at this

end Artform
