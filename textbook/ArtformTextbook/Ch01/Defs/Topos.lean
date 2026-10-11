import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import ArtformTextbook.Meta.Book

/-!
# Subobject classifier, exponentials and topos (Section 1.10, the Category Café)

The book's definitions, written with Mathlib's categories, terminal objects,
binary products and pullback squares (Definitions 1.15, 1.21 and 1.24 of the
book are Mathlib's `Category`, binary product and `IsPullback`).
-/

namespace Artform

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- **Definition 1.28** (subobject classifier). An arrow `true : 1 ⟶ Ω` from a
terminal object is a subobject classifier when every monomorphism `m : S ⟶ X`
is the pullback of `true` along exactly one arrow `χ : X ⟶ Ω`. -/
@[book "def:topos-book"]
def IsSubobjectClassifier {one : C} (hone : IsTerminal one) (Ω : C) (tru : one ⟶ Ω) : Prop :=
  ∀ ⦃S X : C⦄ (m : S ⟶ X), Mono m → ∃! χ : X ⟶ Ω, IsPullback m (hone.from S) χ tru

/-- **Definition 1.23** (exponential). In a category with binary products,
every pair `A`, `B` has an object `E` (written `B^A`) with an evaluation
`ev : E × A ⟶ B` such that every `h : Z × A ⟶ B` is `ev ∘ (λh × 1_A)` for
exactly one `λh : Z ⟶ E`. -/
@[book "def:exponential-book"]
def HasExponentials (C : Type u) [Category.{v} C] [HasBinaryProducts C] : Prop :=
  ∀ A B : C, ∃ (E : C) (ev : E ⨯ A ⟶ B),
    ∀ (Z : C) (h : Z ⨯ A ⟶ B), ∃! g : Z ⟶ E, prod.map g (𝟙 A) ≫ ev = h

/-- **Definition 1.28** (topos): a category with a terminal object, pullbacks,
exponentials and a subobject classifier. Exponentials are defined in a
category with binary products (Definition 1.23), so the products are part of
the condition. -/
@[book "def:topos-book"]
def IsTopos (C : Type u) [Category.{v} C] : Prop :=
  HasTerminal C ∧ HasPullbacks C ∧
  (∃ h : HasBinaryProducts C, @HasExponentials C _ h) ∧
  ∃ (one : C) (hone : IsTerminal one) (Ω : C) (tru : one ⟶ Ω),
    IsSubobjectClassifier hone Ω tru

end Artform
