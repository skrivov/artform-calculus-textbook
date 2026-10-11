import ArtformTextbook.Ch06.Defs.Maxwell

/-!
# The statements of Chapter 6

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

/-- **Theorem 6.1** (reversibility). For fixed source current `J`, the Maxwell
macro-tick is bijective on the finite state space. Lean states it on every
canvas, the chapter's window among them. -/
@[book "thm:reversible"]
def reversible : Prop :=
  ∀ (K : Canvas) (J : K.E → ZMod 8), Function.Bijective (maxwellTick K J)

end Artform.Statement
