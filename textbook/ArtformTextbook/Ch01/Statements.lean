import Mathlib.Data.Fintype.Defs
import Mathlib.CategoryTheory.FintypeCat
import ArtformTextbook.Ch01.Defs.Rods
import ArtformTextbook.Ch01.Defs.Topos

/-!
# The statements of Chapter 1

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

open CategoryTheory CategoryTheory.Limits

/-- **Proposition 1.3** (uniqueness of rod alignment). Between two finite
linearly ordered rods there is at most one perfect alignment. -/
@[book "prop:rod-alignment-unique"]
def rodAlignmentUnique : Prop :=
  ∀ (P Q : Type) [Fintype P] [Fintype Q] [LinearOrder P] [LinearOrder Q]
    (α β : Align P Q), α = β

/-- **Proposition 1.31** (the laws of a rod). For every rod `X` the order on
`cells(X)` is a linear order: no cell comes before itself; if `a` comes before
`b` and `b` before `c`, then `a` comes before `c`; and of two different cells
one comes before the other. -/
@[book "prop:rod-laws"]
def rodLaws : Prop :=
  ∀ X : OrderedForm,
    (∀ a : X.cells, ¬ X.before a a) ∧
    (∀ a b c : X.cells, X.before a b → X.before b c → X.before a c) ∧
    (∀ a b : X.cells, a ≠ b → X.before a b ∨ X.before b a)

/-- **Proposition 1.29** (sets form a topos). `FinSet` and `Set` are topoi,
with `Ω = {0,1}` and `true(*) = 1`. `Set` is Lean's category of types, whose
arrows are functions (`TypeCat.ofHom`), and `FinSet` is Mathlib's category of
finite types. -/
@[book "prop:finset-topos-book"]
def finsetTopos : Prop :=
  IsTopos Type ∧ IsTopos FintypeCat.{0} ∧
  (∃ hone : IsTerminal (PUnit.{1} : Type),
    IsSubobjectClassifier hone (Fin 2) (TypeCat.ofHom fun _ => (1 : Fin 2))) ∧
  (∃ hone : IsTerminal (FintypeCat.of PUnit.{1}),
    IsSubobjectClassifier hone (FintypeCat.of (Fin 2)) (FintypeCat.homMk fun _ => (1 : Fin 2)))

end Artform.Statement
