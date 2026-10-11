import Mathlib.CategoryTheory.Adjunction.Basic
import ArtformTextbook.Ch01.Defs.Cafe
import ArtformTextbook.Ch01.Defs.Topos

/-!
# The statements of the Category Café (Section 1.10)

Each statement of the book is a proposition here, tagged with the book's label. Its proof,
in `ArtformTextbook/Ch01/Cafe.lean`, is a theorem whose type is exactly this proposition.

The declared frames and operations are a quiver on a type `F` of frames, and `ArtSyn F` is
the Artform category `Art^syn` (`ArtformTextbook/Ch01/Defs/Cafe.lean`).
-/

namespace Artform.Statement

open CategoryTheory

universe w v u

/-- **Proposition 1.16** (the Artform category). Finite composable lists of the declared
operations form a category with the frames as objects. For any declared frames `F` and
operations: concatenation of lists (`Quiver.Path.comp`, first `f`, then `g`) is associative and
has the empty lists (`Quiver.Path.nil`) as units, and the Artform category `ArtSyn F` is the
category of these lists, with the empty lists as identities and concatenation as composition.
Any equivalence relation `r` on parallel lists that is preserved by composition (if `f ~ f'`
and `g ~ g'` are composable, then `g ∘ f ~ g' ∘ f'`) gives a quotient category: a category `Q`
with a functor `π : Art^syn ⥤ Q` that presents `Q` as the quotient of `Art^syn` by `r`
(`IsQuotientBy`: `π` is a bijection on objects, every arrow of `Q` is the image of a list, and
two parallel lists have the same image exactly when `r` relates them). -/
@[book "prop:artform-category-book"]
def artformCategory : Prop :=
  ∀ (F : Type u) [Quiver.{v} F],
    (∀ ⦃A B C D : F⦄ (f : Quiver.Path A B) (g : Quiver.Path B C) (h : Quiver.Path C D),
      (f.comp g).comp h = f.comp (g.comp h)) ∧
    (∀ ⦃A B : F⦄ (f : Quiver.Path A B),
      Quiver.Path.nil.comp f = f ∧ f.comp Quiver.Path.nil = f) ∧
    (∀ A : ArtSyn F, 𝟙 A = (Quiver.Path.nil : Quiver.Path (V := F) A A)) ∧
    (∀ ⦃A B C : ArtSyn F⦄ (f : A ⟶ B) (g : B ⟶ C), f ≫ g = Quiver.Path.comp (V := F) f g) ∧
    ∀ r : HomRel (ArtSyn F), (∀ A B : ArtSyn F, Equivalence (@r A B)) →
      (∀ ⦃A B C : ArtSyn F⦄ (f f' : A ⟶ B) (g g' : B ⟶ C),
        r f f' → r g g' → r (f ≫ g) (f' ≫ g')) →
      ∃ (Q : Type u) (_ : Category.{max u v} Q) (π : ArtSyn F ⥤ Q), IsQuotientBy r π

/-- **Proposition 1.19** (the semantic quotient). Let the declared frames and operations have
a state interpretation `S : Art^syn ⥤ Set`. State-equivalence is preserved by composition: if
`f ~ f'` and `g ~ g'` are composable, then `g ∘ f ~ g' ∘ f'`. The quotient of `Art^syn` by it
is a category: a category `Q` with a functor `π : Art^syn ⥤ Q` that presents `Q` as the
quotient of `Art^syn` by state-equivalence (`IsQuotientBy`). Its state interpretation, the
functor `S_Q : Q ⥤ Set` with `S_Q ∘ π = S`, is faithful: distinct arrows between the same two
frames denote distinct functions. -/
@[book "prop:semantic-quotient-book"]
def semanticQuotient : Prop :=
  ∀ (F : Type u) [Quiver.{v} F] (S : StateInterpretation.{w} F),
    (∀ ⦃A B C : ArtSyn F⦄ (f f' : A ⟶ B) (g g' : B ⟶ C),
      S.StateEquivalent f f' → S.StateEquivalent g g' →
        S.StateEquivalent (f ≫ g) (f' ≫ g')) ∧
    ∃ (Q : Type u) (_ : Category.{max u v} Q) (π : ArtSyn F ⥤ Q) (SQ : Q ⥤ Type w),
      IsQuotientBy S.StateEquivalent π ∧ π ⋙ SQ = S.functor ∧ SQ.Faithful

/-- **Proposition 1.27** (adjoints of reindexing). In the set interpretation,
`Σ_f ⊣ f^* ⊣ Π_f`: for every map `f : J → I`, there are bijections
`Hom(Σ_f E, B) ≅ Hom(E, f^* B)` and `Hom(f^* B, E) ≅ Hom(B, Π_f E)` for every family `E` over
`J` and `B` over `I`, natural in `E` and `B`. That is, `Σ_f` is left adjoint to `f^*`, and `f^*`
is left adjoint to `Π_f` (Definition 1.26, Mathlib's `Adjunction`), between the categories
`Fam(J)` and `Fam(I)` of families of sets. -/
@[book "prop:adjoints-book"]
def adjoints : Prop :=
  ∀ (I J : Type u) (f : J → I),
    Nonempty (Fam.sigma f ⊣ Fam.reindex f) ∧ Nonempty (Fam.reindex f ⊣ Fam.pi f)

/-- **Proposition 1.30** (the Artform category is not a topos). `Art^syn` is a topos only when
it has one frame and no operation: if the Artform category of the declared frames `F` and
operations is a topos (Definition 1.28), then there is exactly one frame, and no declared
operation. -/
@[book "prop:artform-not-topos-book"]
def artformNotTopos : Prop :=
  ∀ (F : Type u) [Quiver.{v} F], IsTopos (ArtSyn F) →
    (∃ A : F, ∀ B : F, B = A) ∧ ∀ A B : F, IsEmpty (A ⟶ B)

end Artform.Statement
