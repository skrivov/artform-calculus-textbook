import ArtformStages.Basic

/-!
# One mark on a space

A *filling* of one mark puts a number of a dial `R` at finitely many laws of a space `G`,
and is 0 at the others. Fillings multiply as the group ring `R[G]` does: a filling of one
place at rest is `1`. In the charter's thirteenth edition (D16) a wave in whole numbers is
such a filling, and the hop of an act is the table of one stencil.

* `law_eq_mul_stencil`: a law of one mark that adds and is the same at every place is
  the table of one stencil: `f` goes to `f * T 1`.
* `eq_single_of_mul_eq_one`: on a space with two unique products, on a dial without zero
  divisors, two fillings whose product is `1` have one place each.
* `law_of_one_mark_is_a_shift`: so a law of one mark that adds, is the same at every place
  and can be undone is a shift: `f` goes to `f * single g r`.
* Every lattice, of rows that pass in any number, is such a space.

The Hantzsche-Wendt space is not: there G. Gardam's filling of 21 places on the dial of 2
has a way back. That is checked by a script in the research ledger, not here.

No statement here is new: it is the classical proof that a group with unique products
has only the trivial units in its group ring.
-/

open MonoidAlgebra Finset

namespace Artform.Stages

variable {R G : Type*}

/-- **One rule is one stencil.** A law of one mark that adds and is the same at every
place, which is to say a map of fillings that passes every filling put before it, is the
table of one stencil: the filling that it makes of one mark at rest. -/
theorem law_eq_mul_stencil [Semiring R] [Monoid G] (T : R[G] →ₗ[R[G]] R[G]) (f : R[G]) :
    T f = f * T 1 := by
  have h := T.map_smul f 1
  rwa [smul_eq_mul, mul_one, smul_eq_mul] at h

section TwoUniqueProds

variable [Semiring R] [NoZeroDivisors R] [Monoid G] [TwoUniqueProds G]

/-- Two fillings whose product is one mark at rest have, between them, one pair of places. -/
theorem card_support_mul_le_one_of_mul_eq_one {u v : R[G]} (h : u * v = 1) :
    #u.coeff.support * #v.coeff.support ≤ 1 := by
  classical
  by_contra hc
  rw [not_le] at hc
  obtain ⟨p1, h1, p2, h2, hne, hu1, hu2⟩ := TwoUniqueProds.uniqueMul_of_one_lt_card hc
  rw [Finset.mem_product] at h1 h2
  have c1 : (u * v).coeff (p1.1 * p1.2) ≠ 0 := by
    rw [coeff_mul_mul_of_uniqueMul hu1]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp h1.1) (Finsupp.mem_support_iff.mp h1.2)
  have c2 : (u * v).coeff (p2.1 * p2.2) ≠ 0 := by
    rw [coeff_mul_mul_of_uniqueMul hu2]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp h2.1) (Finsupp.mem_support_iff.mp h2.2)
  have one_only : ∀ g : G, (1 : R[G]).coeff g ≠ 0 → g = 1 := by
    intro g hg
    by_contra hg1
    apply hg
    rw [one_def, coeff_single]
    exact Finsupp.single_eq_of_ne hg1
  rw [h] at c1 c2
  have e := hu1 h2.1 h2.2 ((one_only _ c2).trans (one_only _ c1).symm)
  exact hne (Prod.ext e.1.symm e.2.symm)

/-- **Only the shifts.** On a space with two unique products, on a dial without zero
divisors, two fillings whose product is one mark at rest have one place each. -/
theorem eq_single_of_mul_eq_one [Nontrivial R] {u v : R[G]} (h : u * v = 1) :
    ∃ g k : G, ∃ r s : R, u = single g r ∧ v = single k s ∧ g * k = 1 ∧ r * s = 1 := by
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact zero_ne_one h
  have hv : v ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact zero_ne_one h
  have cu : 1 ≤ #u.coeff.support :=
    Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr (coeff_eq_zero.not.mpr hu))
  have cv : 1 ≤ #v.coeff.support :=
    Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr (coeff_eq_zero.not.mpr hv))
  have le := card_support_mul_le_one_of_mul_eq_one h
  have cu1 : #u.coeff.support = 1 :=
    le_antisymm ((Nat.le_mul_of_pos_right _ cv).trans le) cu
  have cv1 : #v.coeff.support = 1 :=
    le_antisymm ((Nat.le_mul_of_pos_left _ cu).trans le) cv
  obtain ⟨g, r, -, hr⟩ := Finsupp.card_support_eq_one'.mp cu1
  obtain ⟨k, s, -, hs⟩ := Finsupp.card_support_eq_one'.mp cv1
  have eu : u = single g r := coeff_injective (by rw [hr, coeff_single])
  have ev : v = single k s := coeff_injective (by rw [hs, coeff_single])
  refine ⟨g, k, r, s, eu, ev, ?_⟩
  rw [eu, ev, single_mul_single, one_def] at h
  have h' := congrArg coeff h
  rw [coeff_single, coeff_single, Finsupp.single_eq_single_iff] at h'
  rcases h' with ⟨h1, h2⟩ | ⟨-, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd h2 one_ne_zero

/-- **One mark on a space with unique products has no law but the shifts.** A law of one
mark that adds, is the same at every place and can be undone sends every filling `f` to
`f * single g r`: it is the shift by one law `g`, with one number `r`. -/
theorem law_of_one_mark_is_a_shift [Nontrivial R] (T : R[G] ≃ₗ[R[G]] R[G]) :
    ∃ g : G, ∃ r : R, ∀ f : R[G], T f = f * single g r := by
  have key : T.symm 1 * T 1 = 1 := by
    have h := law_eq_mul_stencil (T : R[G] →ₗ[R[G]] R[G]) (T.symm 1)
    rw [LinearEquiv.coe_coe, T.apply_symm_apply] at h
    exact h.symm
  obtain ⟨-, k, -, s, -, hv, -, -⟩ := eq_single_of_mul_eq_one key
  refine ⟨k, s, fun f => ?_⟩
  rw [← hv]
  exact law_eq_mul_stencil (T : R[G] →ₗ[R[G]] R[G]) f

end TwoUniqueProds

/-- Every lattice has two unique products: rows that pass, in any number `d`. -/
instance lattice_twoUniqueProds (d : ℕ) : TwoUniqueProds (Multiplicative (Fin d → ℤ)) :=
  inferInstance

/-- **On a lattice one mark has no law but the shifts**, on the whole numbers and on
every dial without zero divisors, in any number `d` of dimensions. -/
theorem lattice_law_of_one_mark_is_a_shift [Semiring R] [NoZeroDivisors R] [Nontrivial R] (d : ℕ)
    (T : R[Multiplicative (Fin d → ℤ)] ≃ₗ[R[Multiplicative (Fin d → ℤ)]]
      R[Multiplicative (Fin d → ℤ)]) :
    ∃ g : Multiplicative (Fin d → ℤ), ∃ r : R, ∀ f, T f = f * single g r :=
  law_of_one_mark_is_a_shift T

/-- The same for a stage, when its laws have two unique products. -/
theorem Stage.law_of_one_mark_is_a_shift {α : Type*} [Semiring R] [NoZeroDivisors R] [Nontrivial R]
    (S : Stage α) [TwoUniqueProds S.World] (T : R[S.World] ≃ₗ[R[S.World]] R[S.World]) :
    ∃ w : S.World, ∃ r : R, ∀ f, T f = f * single w r :=
  Artform.Stages.law_of_one_mark_is_a_shift T

end Artform.Stages
