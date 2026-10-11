import ArtformTextbook.Ch03.Defs.Receipts

/-!
# Statements of Chapter 3: receipts and margins

Each statement of the book is a proposition here, tagged with the book's label. Its proof,
elsewhere in the chapter's folder, is a theorem whose type is exactly this proposition.
-/

namespace Artform.Statement

open Receipts

/-- **Proposition 3.43** (receipts decide, and margins protect). Each receipt above is decided by
finitely many comparisons of rational numbers, so every accepted receipt is an exact finite
verdict. Let a second sampled picture be supplied with bijections of the parts and of their pixel
regions that preserve pixel adjacency, boundaries, joint sites and the complete candidate
inventories, and let every inequality of every receipt change by less than its recorded margin.
Then every verdict is preserved and the two observations produce the same feature state.

Partial (the author's decision for tier E, 2026-10-11). Lean proves:
1. Each of the six receipts (elongated, round, connected, joint, angle band, proportion) is
   decided by the comparisons the book lists: its verdict is the book's condition on those
   comparisons of rationals and on the combinatorial data it reads.
2. Margins protect every receipt: if each comparison of a receipt changes by less than its
   recorded margin, the absolute slack `|R - L|`, and the data it reads are the same, its
   verdict is the same.
3. Two observations under one protocol, with a bijection of their parts under which the data
   every receipt reads correspond and every comparison changes by less than its margin, produce
   the same feature state, read through the bijection.

Not formalized: the sampled pictures themselves, pixel by pixel, and the observation that turns
them into parts and numbers. The numbers each receipt compares (the spreads `A_U`, `T_U`, the
radii `r₋`, `r₊`, the distance `d_q`, the inner products and squared lengths) enter as rational
inputs, and the combinatorial data the bijections preserve (connectivity, nonempty boundaries,
ports and joint sites, membership of the candidates) enter as data the receipts read. A
comparison's recorded margin is read as its absolute slack in the first picture, and "change by
less than" as the slack moving by less than that; the bijection of the parts identifies the atoms
of the two observations, and the complete inventories give the two pictures' receipts the same
comparisons. -/
@[book "prop:metric-feature-receipts-book"]
def metricFeatureReceipts : Prop :=
  (∀ (Ax : Type) [Fintype Ax] (m n : ℚ) (A T : Ax → ℚ) (conn : Bool) (ends : Ax → Bool),
    (elongatedR Ax).eval (conn, ends) (elongatedCmps m n A T) =
      if conn = true ∧ ∃ u, ends u = true ∧ m * T u ≤ n * A u then some true
      else if conn = false ∨ ∀ u, n * A u < m * T u then some false else none) ∧
  (∀ (m n rMinus rPlus : ℚ) (conn bdry : Bool),
    roundR.eval (conn, bdry) (roundCmps m n rMinus rPlus) =
      decide (conn = true ∧ bdry = true ∧ 0 < rMinus ∧ n * rPlus ≤ m * rMinus)) ∧
  (∀ (dq delta2 : ℚ) (bU bV : Bool),
    connectedR.eval (bU, bV) (connectedCmps dq delta2) =
      decide (bU = true ∧ bV = true ∧ dq ≤ delta2)) ∧
  (∀ (dq delta2 : ℚ) (bU bV ports : Bool),
    jointR.eval ((bU, bV), ports) (connectedCmps dq delta2) =
      decide (bU = true ∧ bV = true ∧ ports = true ∧ dq ≤ delta2)) ∧
  (∀ (a b qu qv p : ℚ) (nonzero : Bool),
    angleR.eval nonzero (angleCmps a b qu qv p) =
      decide (nonzero = true ∧ a * qu * qv ≤ p ^ 2 ∧ p ^ 2 ≤ b * qu * qv)) ∧
  (∀ (lMinus lPlus qu qv : ℚ),
    proportionR.eval () (proportionCmps lMinus lPlus qu qv) =
      decide (lMinus * qv ≤ qu ∧ qu ≤ lPlus * qv)) ∧
  (∀ (D V : Type) (R : Receipt D V) (d : D) (c c' : R.I → Cmp),
    (∀ i, (c i).WithinMargin (c' i)) → R.eval d c' = R.eval d c) ∧
  ∀ (D V : Type) (π : Protocol D V) (o₁ o₂ : Observation π) (e : o₁.Part ≃ o₂.Part),
    (∀ r t, o₂.data r (e ∘ t) = o₁.data r t) →
    (∀ r t i, (o₁.cmps r t i).WithinMargin (o₂.cmps r (e ∘ t) i)) →
    ∀ r t, o₂.featureState r (e ∘ t) = o₁.featureState r t

end Artform.Statement
