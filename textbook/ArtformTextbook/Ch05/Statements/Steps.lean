import ArtformTextbook.Ch05.Defs.Steps

/-!
# Statements of Chapter 5: laws in steps

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

/-- **Theorem 5.13** (finite well-posedness). Let a law in steps have a
well-posed deterministic realizer. From every legal start, over every finite
stretch of the score, the realizer has exactly one run. The order in which
the moves of each batch are applied does not change its states, and every
invariant holds at each of its checkpoints.

The stretch is the `n` slots that begin at slot `s`; the start is legal at
boundary `s`. A run follows the realizer when each of its steps applies the
batch the realizer selects; it is unique among all such runs, and its states
are then legal at every boundary of the stretch. -/
@[book "thm:well-posed"]
def finiteWellPosedness : Prop :=
  ∀ (A : Presentation) (L : LawInSteps A) (R : L.DetRealizer), R.WellPosed →
    ∀ (s n : ℕ) (x₀ : A.Table), L.LegalAt s x₀ →
      (∃! r : Run A n, r.state 0 = x₀ ∧ r.Follows R s) ∧
      ∀ r : Run A n, r.state 0 = x₀ → r.Follows R s →
        (∀ (i : Fin n) (l : List (EnabledApp A (r.state i.castSucc))),
          l.Perm (r.batch i).apps → applyAll l (r.state i.castSucc) = r.state i.succ) ∧
        ∀ i : Fin (n + 1), ∀ J ∈ L.invariants, s + (i : ℕ) ∈ J.checkpoints → J.holds (r.state i)

end Artform.Statement
