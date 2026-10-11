import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types.Basic
import ArtformTextbook.Meta.Book

/-!
# The Artform category, its quotients and families of sets (Section 1.10, the Category Café)

* `ArtSyn F` is the Artform category `Art^syn` of declared frames and operations.
  The declared data are a quiver on the type `F` of frames: `A ⟶ B` (for `A B : F`) is the
  type of declared operations with source `A` and target `B`. The arrows of `ArtSyn F` are
  the finite composable lists of operations, and it is Mathlib's free category `Paths F`.
* `IsQuotientBy r π` says that a functor `π` presents its target as the quotient category of
  its source by a relation `r` on parallel arrows.
* `StateInterpretation F` gives the legal states of each frame and the legal-state function
  of each operation. Its `functor` is the state interpretation `S : Art^syn ⥤ Set`, and
  `StateEquivalent` is state-equivalence of parallel scripts.
* `Fam I` is the category `Fam(I)` of families of sets over `I`, with reindexing
  `Fam.reindex f` (the book's `f^*`) and the two binders over the fibres of `f`,
  `Fam.sigma f` (`Σ_f`) and `Fam.pi f` (`Π_f`).

The book's Definitions 1.15 (category), 1.18 (functor), 1.20 (natural transformation),
1.21 (product), 1.24 (pullback) and 1.26 (adjunction) are Mathlib's `Category`, `Functor`,
`NatTrans`, binary products (`HasBinaryProducts`, `prod.lift`), `IsPullback` and `Adjunction`.
Mathlib's `Adjunction` stores a unit and a counit; its `homEquiv` is the book's bijection
`Hom(F A, B) ≅ Hom(A, G B)`, natural in both variables, and `Adjunction.mkOfHomEquiv` builds an
adjunction from such a bijection. `Set` is Lean's category `Type w`, whose arrows are functions
(`TypeCat.ofHom`).
-/

namespace Artform

open CategoryTheory

universe w v u u' v'

/-! ## The Artform category -/

/-- The Artform category `Art^syn` of the declared frames `F` and operations: the objects
are the frames, an arrow `A ⟶ B` is a finite composable list of declared operations whose
first source is `A` and whose last target is `B` (a `Quiver.Path A B`), the identity `1_A` is
the empty list at `A`, and composition is concatenation (`f ≫ g` is `f.comp g`, first `f`, then
`g`; the book writes it `g ∘ f`). Two scripts are equal when their lists of operations are
equal. This is Mathlib's free category `Paths F` on the quiver of declared operations. -/
abbrev ArtSyn (F : Type u) [Quiver.{v} F] : Type u := Paths F

/-- The functor `π : C ⥤ Q` presents `Q` as the quotient category of `C` by the relation `r`
on parallel arrows: `π` is a bijection on objects, every arrow of `Q` between images is the
image of an arrow of `C`, and two parallel arrows of `C` have the same image exactly when `r`
relates them. The arrows `π A ⟶ π B` are then the classes of `r` on the arrows `A ⟶ B`, and
`π (f ≫ g) = π f ≫ π g` says that classes compose by `[g] ∘ [f] = [g ∘ f]`. -/
def IsQuotientBy {C : Type u} [Category.{v} C] {Q : Type u'} [Category.{v'} Q]
    (r : HomRel C) (π : C ⥤ Q) : Prop :=
  Function.Bijective π.obj ∧ π.Full ∧ ∀ ⦃A B : C⦄ (f g : A ⟶ B), π.map f = π.map g ↔ r f g

/-! ## The state interpretation -/

/-- A state interpretation of declared frames and operations: each frame `A` has the type
`State A` of its legal states, and each declared operation `o : A ⟶ B` has its legal-state
function `act o : State A → State B`. A guarded move has as its source a frame whose states
carry the required evidence, so every action is total on the states of its source. -/
structure StateInterpretation (F : Type u) [Quiver.{v} F] where
  /-- The legal states of a frame. -/
  State : F → Type w
  /-- The legal-state function of a declared operation. -/
  act : ∀ {A B : F}, (A ⟶ B) → State A → State B

namespace StateInterpretation

variable {F : Type u} [Quiver.{v} F] (S : StateInterpretation.{w} F)

/-- The frames and operations sent to their legal states and legal-state functions. -/
def prefunctor : F ⥤q Type w where
  obj := S.State
  map o := TypeCat.ofHom (S.act o)

/-- The state interpretation `S : Art^syn ⥤ Set`: `S(A) = State(A)`, and a script goes to its
legal-state function, the composite of the actions of its operations (the empty script acts as
the identity). It is the functor from the free category given by `prefunctor`. -/
def functor : ArtSyn F ⥤ Type w :=
  Paths.lift S.prefunctor

/-- Two parallel scripts are state-equivalent when their state functions agree on every legal
input. -/
def StateEquivalent : HomRel (ArtSyn F) :=
  fun _ _ f g => ∀ x, S.functor.map f x = S.functor.map g x

end StateInterpretation

/-! ## Families of sets -/

/-- `Fam I`, the families of sets over `I`: a family `B` assigns a set `B i` to each `i : I`.
Its category is Mathlib's product category `CategoryTheory.pi`: an arrow `B ⟶ B'` is a
function `B i → B' i` for every `i`, composed index by index. -/
abbrev Fam (I : Type u) : Type (u + 1) := I → Type u

namespace Fam

variable {I J : Type u}

/-- Reindexing along `f : J → I`, the book's `f^* : Fam(I) ⥤ Fam(J)`: `(f^* B)(j) = B(f(j))`,
acting on arrows by the same fibre maps. It is Mathlib's `Pi.comap`. -/
def reindex (f : J → I) : Fam I ⥤ Fam J :=
  Pi.comap (fun _ : I => Type u) f

/-- The tagged choice over the fibres of `f : J → I`, the book's `Σ_f : Fam(J) ⥤ Fam(I)`:
`(Σ_f E)(i) = Σ_{j : f⁻¹(i)} E(j)`, where `f⁻¹(i) = {j // f j = i}`. An arrow acts on the
entry and keeps the index. -/
def sigma (f : J → I) : Fam J ⥤ Fam I where
  obj E i := Σ j : {j : J // f j = i}, E j
  map φ _ := TypeCat.ofHom fun x => ⟨x.1, φ x.1.1 x.2⟩

/-- The complete assignment over the fibres of `f : J → I`, the book's `Π_f : Fam(J) ⥤ Fam(I)`:
`(Π_f E)(i) = Π_{j : f⁻¹(i)} E(j)`, where `f⁻¹(i) = {j // f j = i}`. An arrow acts on every
entry. -/
def pi (f : J → I) : Fam J ⥤ Fam I where
  obj E i := ∀ j : {j : J // f j = i}, E j
  map φ _ := TypeCat.ofHom fun s j => φ j.1 (s j)

end Fam

end Artform
