import ArtformTextbook.Ch02.Defs.Process

/-!
# Statements of Chapter 3: growth

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

/-- **Proposition 3.27** (commuting compatible changes). If two enabled
applications are compatible, making one and then the other gives the same
state in either order. -/
@[book "prop:commuting-proposals"]
def commutingProposals : Prop :=
  ∀ (A : Presentation) (x : A.Table) (a b : EnabledApp A x), a.Compatible b →
    b.profile.apply (a.profile.apply x) = a.profile.apply (b.profile.apply x)

end Artform.Statement
