import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Types.Basic
import ArtformTextbook.Meta.Book

/-!
# Subcategories (*Category Café: a categorical view of artform calculus* ◊)

Definition 1.17: a subcategory selects objects and arrows of a category,
keeps the identity of every selected object, and is closed under composition;
it is full when it keeps every arrow between its selected objects.

Mathlib has the two special cases: `ObjectProperty.FullSubcategory` (full, any
selected objects) and `WideSubcategory` (every object, a multiplicative class
of arrows). A general subcategory selects both, so it is defined here, with
the category it is (`Subcategory.Obj`): composition and the equality of arrows
are those of the ambient category.
-/

namespace Artform

open CategoryTheory

universe v u

/-- **Definition 1.17** (subcategory). A subcategory `𝒟` of `𝒞` selects
objects and arrows of `𝒞`; the source and the target of a selected arrow are
selected, the identity of every selected object is selected, and the selected
arrows are closed under composition. -/
@[book "def:subcategory-book"]
structure Subcategory (C : Type u) [Category.{v} C] where
  /-- The selected objects. -/
  obj : Set C
  /-- The selected arrows. -/
  arr : MorphismProperty C
  /-- The source of a selected arrow is selected. -/
  src_mem : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), arr f → X ∈ obj
  /-- The target of a selected arrow is selected. -/
  tgt_mem : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), arr f → Y ∈ obj
  /-- The identity of every selected object is selected. -/
  id_mem : ∀ X ∈ obj, arr (𝟙 X)
  /-- The selected arrows are closed under composition. -/
  comp_mem : ∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z), arr f → arr g → arr (f ≫ g)

namespace Subcategory

variable {C : Type u} [Category.{v} C] (D : Subcategory C)

/-- **Definition 1.17** (full subcategory): it keeps every arrow of `𝒞` between
its selected objects. -/
@[book "def:subcategory-book"]
def Full : Prop := ∀ X ∈ D.obj, ∀ Y ∈ D.obj, ∀ f : X ⟶ Y, D.arr f

/-- The objects of the subcategory. -/
def Obj : Type u := {X : C // X ∈ D.obj}

/-- The subcategory is a category: its arrows are the selected arrows, and it
inherits composition and the equality of arrows from `𝒞`. -/
instance : Category.{v} D.Obj where
  Hom X Y := {f : X.1 ⟶ Y.1 // D.arr f}
  id X := ⟨𝟙 X.1, D.id_mem X.1 X.2⟩
  comp f g := ⟨f.1 ≫ g.1, D.comp_mem f.1 g.1 f.2 g.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

end Subcategory

/-! ## Non-vacuity -/

/-- In the category of sets, the sets with at most one element and all the
functions between them form a full subcategory. -/
example : ∃ D : Subcategory (Type u), D.Full := by
  refine ⟨⟨{X | Subsingleton X}, fun X Y _ => Subsingleton X ∧ Subsingleton Y,
    fun _ _ _ h => h.1, fun _ _ _ h => h.2, fun _ hX => ⟨hX, hX⟩,
    fun _ _ _ _ _ hf hg => ⟨hf.1, hg.2⟩⟩, ?_⟩
  exact fun _ hX _ hY _ => ⟨hX, hY⟩

end Artform
