import ArtformTextbook.Ch05.Defs.GaugeLaw

/-!
# Statements of Chapter 5: gauge covariance passes to runs

Each statement of the book is a proposition here, tagged with the book's
label. Its proof, elsewhere in the chapter's folder, is a theorem whose type
is exactly this proposition.
-/

namespace Artform.Statement

/-- **Proposition 5.36** (gauge covariance passes to runs). For a gauge-covariant
law with a gauge-covariant deterministic realizer, `F(h · x) = h · F(x)` for
every gauge change `h` and every legal state `x`. The runs from `x` and from
`h · x` are related tick by tick by `h`, and every gauge-invariant reading takes
the same values along both.

Here `F` is the tick (Definition 5.1) that the realizer makes: the batch it
selects at a state (Definition 5.10), applied. A run of the realizer is a run
whose states are legal and whose every step applies the batch the realizer
selects (`Run.OfDet`); the runs from `x` and from `h · x` are any two such
runs over the same ticks, the first starting at `x` and the second at `h · x`.
A run carries its trace, so the two are related tick by tick in two ways: the
state of the second is `h` applied to the state of the first, and the second
makes the same moves as the first, perhaps listed in another order. A reading
is a map `q` of the states, to any type; as in the book's proof, the reading
is asked only to have `q(h · y) = q(y)` at every state `y`, for the gauge
change `h` at hand, which every gauge-invariant reading has.

The first part is stated for a law of Definition 5.9 (`Law`). The second
states the same, slot by slot, for a law in steps of Definition 5.12
(`LawInSteps`), whose realizer selects a batch in every slot: there `F` is the
map of one slot, at every state legal at the slot's opening boundary, and the
runs follow the realizer over the same stretch of the score, the first from a
state legal at its first boundary; they are related at every boundary, so at
every tick. -/
@[book "prop:gauge-runs"]
def gaugeRuns : Prop :=
  (∀ (A : Presentation) (𝒢 : Type) (α : GaugeAction A 𝒢) (L : Law A) (R : DetRealizer L),
    L.GaugeCovariant α → R.GaugeCovariant α →
      (∀ (h : 𝒢) (x : A.Table), L.Legal x →
        (R.select (α.smul h x)).apply = α.smul h (R.select x).apply) ∧
      ∀ (h : 𝒢) (n : ℕ) (r r' : Run A n), r.OfDet R → r'.OfDet R →
        r'.state 0 = α.smul h (r.state 0) →
          (∀ i, r'.state i = α.smul h (r.state i)) ∧
          (∀ i, (r'.batch i).moves.Perm (r.batch i).moves) ∧
          ∀ (Q : Type) (q : A.Table → Q), (∀ y : A.Table, q (α.smul h y) = q y) →
            ∀ i, q (r'.state i) = q (r.state i)) ∧
  ∀ (A : Presentation) (𝒢 : Type) (α : GaugeAction A 𝒢) (L : LawInSteps A)
    (R : L.DetRealizer), L.GaugeCovariant α → R.GaugeCovariant α →
      (∀ (t : ℕ) (h : 𝒢) (x : A.Table), L.LegalAt t x →
        (R.select t (α.smul h x)).apply = α.smul h (R.select t x).apply) ∧
      ∀ (h : 𝒢) (s n : ℕ) (r r' : Run A n), L.LegalAt s (r.state 0) →
        r.Follows R s → r'.Follows R s → r'.state 0 = α.smul h (r.state 0) →
          (∀ i, r'.state i = α.smul h (r.state i)) ∧
          (∀ i, (r'.batch i).moves.Perm (r.batch i).moves) ∧
          ∀ (Q : Type) (q : A.Table → Q), (∀ y : A.Table, q (α.smul h y) = q y) →
            ∀ i, q (r'.state i) = q (r.state i)

end Artform.Statement
