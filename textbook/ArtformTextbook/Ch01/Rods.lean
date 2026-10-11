import Mathlib.Data.Fintype.Sum
import ArtformTextbook.Ch01.Statements

/-!
# Rods: the uniqueness of alignment and the laws of a rod

Proposition 1.3: between two finite linearly ordered rods there is at most one
perfect alignment. A monotone bijection between linear orders is strictly
monotone, so it is an order isomorphism; a finite linear order is well-founded,
and out of a well-founded linear order there is at most one order isomorphism
(Mathlib's `OrderIso.subsingleton_of_wellFoundedLT`). This last fact stands in
for the book's induction, which sends the least cell to the least cell.

Proposition 1.31: the order of Section 1.11 on the cells of every rod is a
linear order, by the elimination rule, comparing tags first in a glued rod.

The non-vacuity section makes the cells of every rod a finite linear order
whose `<` is `before`, from Proposition 1.31, and exhibits the alignment of
Figure 1.9.
-/

namespace Artform

/-- **Proposition 1.3** (uniqueness of rod alignment). Between two finite
linearly ordered rods there is at most one perfect alignment. -/
@[book "prop:rod-alignment-unique"]
theorem rodAlignmentUnique : Statement.rodAlignmentUnique := by
  intro P Q _ _ _ _ α β
  -- A perfect alignment is a monotone bijection, so an order isomorphism.
  let e : Align P Q → P ≃o Q := fun γ =>
    StrictMono.orderIsoOfSurjective γ.1 (γ.2.2.strictMono_of_injective γ.2.1.1) γ.2.1.2
  -- `P` is finite, so well-founded, and has at most one order isomorphism to `Q`.
  exact Subtype.ext (congrArg DFunLike.coe (Subsingleton.elim (e α) (e β)))

/-- **Proposition 1.31** (the laws of a rod). For every rod `X` the order on
`cells(X)` is a linear order: no cell comes before itself; if `a` comes before
`b` and `b` before `c`, then `a` comes before `c`; and of two different cells
one comes before the other. By the elimination rule: for `R_n` these are laws
of the numbers below `n`; in `glue(P, Q)` two cells with different tags stand
`L` before `R`, and two with the same tag stand as in `P` or in `Q`. -/
@[book "prop:rod-laws"]
theorem rodLaws : Statement.rodLaws := by
  intro X
  induction X with
  | rod n => exact ⟨fun a => lt_irrefl a, fun _ _ _ => lt_trans, fun _ _ => lt_or_gt_of_ne⟩
  | glue P Q ihP ihQ =>
    obtain ⟨irrP, transP, totP⟩ := ihP
    obtain ⟨irrQ, transQ, totQ⟩ := ihQ
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_ | _, a⟩
      · exact irrP a
      · exact irrQ a
    · rintro ⟨_ | _, a⟩ ⟨_ | _, b⟩ ⟨_ | _, c⟩ hab hbc
      · exact transP a b c hab hbc
      · exact trivial
      · exact hbc.elim
      · exact trivial
      · exact hab.elim
      · exact hab.elim
      · exact hbc.elim
      · exact transQ a b c hab hbc
    · rintro ⟨_ | _, a⟩ ⟨_ | _, b⟩ hab
      · exact totP a b fun h => hab (h ▸ rfl)
      · exact Or.inl trivial
      · exact Or.inr trivial
      · exact totQ a b fun h => hab (h ▸ rfl)

/-! ## Non-vacuity

Proposition 1.31 makes the cells of every rod a linear order whose `<` is
`before`, and the cells of every rod are finite. With these, the alignment of
Figure 1.9 is an element of `Align`, and by Proposition 1.3 the only one. -/

namespace OrderedForm

/-- Whether one cell of a rod comes before another is decided, by the
elimination rule. -/
instance instDecidableRelBefore : (X : OrderedForm) → DecidableRel X.before
  | rod _ => fun i j => inferInstanceAs (Decidable (i < j))
  | glue P Q => fun a b => match a, b with
    | ⟨.L, p⟩, ⟨.L, p'⟩ => instDecidableRelBefore P p p'
    | ⟨.L, _⟩, ⟨.R, _⟩ => isTrue trivial
    | ⟨.R, _⟩, ⟨.L, _⟩ => isFalse id
    | ⟨.R, q⟩, ⟨.R, q'⟩ => instDecidableRelBefore Q q q'

/-- Proposition 1.31, read as a strict total order. -/
instance instIsStrictTotalOrderBefore (X : OrderedForm) :
    IsStrictTotalOrder X.cells X.before where
  irrefl := (rodLaws X).1
  trans := (rodLaws X).2.1
  trichotomous a b hab hba := by
    by_contra h
    rcases (rodLaws X).2.2 a b h with h' | h'
    exacts [hab h', hba h']

/-- The cells of a rod as a linear order whose `<` is `before`. -/
instance instLinearOrderCells (X : OrderedForm) : LinearOrder X.cells :=
  linearOrderOfSTO X.before

/-- The same order on the cells of a glued rod. Instance search unfolds the
cells of `glue P Q` to a tagged choice, where it does not find the instance
above; for `R_n` it finds the order of `Fin n`, whose `<` is also `before`. -/
instance instLinearOrderCellsGlue (P Q : OrderedForm) : LinearOrder (glue P Q).cells :=
  instLinearOrderCells _

/-- The cells of a rod are finite: those of `glue(P, Q)` are those of `P` and
those of `Q`. -/
instance instFintypeCells : (X : OrderedForm) → Fintype X.cells
  | rod n => inferInstanceAs (Fintype (Fin n))
  | glue P Q =>
    letI := instFintypeCells P
    letI := instFintypeCells Q
    Fintype.ofEquiv (P.cells ⊕ Q.cells)
      { toFun := Sum.elim (fun p => ⟨.L, p⟩) fun q => ⟨.R, q⟩
        invFun := fun
          | ⟨.L, p⟩ => .inl p
          | ⟨.R, q⟩ => .inr q
        left_inv := by rintro (_ | _) <;> rfl
        right_inv := by rintro ⟨_ | _, _⟩ <;> rfl }

/-- The same on the cells of a glued rod, for instance search. -/
instance instFintypeCellsGlue (P Q : OrderedForm) : Fintype (glue P Q).cells :=
  instFintypeCells _

end OrderedForm

/-- The order of the cells of a rod is `before`. -/
example (X : OrderedForm) (a b : X.cells) : a < b ↔ X.before a b := Iff.rfl

/-- Figure 1.9: a perfect alignment of `glue(R₂, R₃)` with `R₅` sends the cells
`L0, L1, R0, R1, R2` to `0, 1, 2, 3, 4`, and by Proposition 1.3 every perfect
alignment of the two rods is this one. -/
example : ∃ α : Align (OrderedForm.glue (.rod 2) (.rod 3)).cells (OrderedForm.rod 5).cells,
    (α.1 ⟨.L, 0⟩, α.1 ⟨.L, 1⟩, α.1 ⟨.R, 0⟩, α.1 ⟨.R, 1⟩, α.1 ⟨.R, 2⟩) = (0, 1, 2, 3, 4) ∧
      ∀ β, β = α := by
  let f : (OrderedForm.glue (.rod 2) (.rod 3)).cells → (OrderedForm.rod 5).cells := fun
    | ⟨.L, i⟩ => Fin.castAdd 3 i
    | ⟨.R, j⟩ => Fin.natAdd 2 j
  have hf : StrictMono f := by
    rintro ⟨_ | _, a⟩ ⟨_ | _, b⟩ hab
    · exact hab
    · exact Nat.lt_of_lt_of_le a.isLt (Nat.le_add_right 2 b)
    · exact hab.elim
    · exact Nat.add_lt_add_left hab 2
  have hs : Function.Surjective f := fun k =>
    Fin.addCases (m := 2) (n := 3) (motive := fun k => ∃ a, f a = k)
      (fun i => ⟨⟨.L, i⟩, rfl⟩) (fun j => ⟨⟨.R, j⟩, rfl⟩) k
  exact ⟨⟨f, ⟨hf.injective, hs⟩, hf.monotone⟩, rfl, fun β => rodAlignmentUnique _ _ β _⟩

end Artform
