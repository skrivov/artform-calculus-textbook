import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import ArtformTextbook.Ch05.Statements

/-!
# Hall's theorem on supplies and demands (Section 5.21)

The proof of Theorem 5.44. The goods are whole numbers, so each store `u` is
split into `s(u)` units of goods and each shop `y` into `d(y)` units of need.
A unit of `u` may go to a unit of `y` when `u` may supply `y`. Hall's marriage
theorem (Mathlib's `Fintype.all_card_le_filter_rel_iff_exists_injective`)
matches the units of goods one to one with units of need; with equal totals the
matching is a bijection, and `x(u, y)` counts the units of `u` matched to `y`.
-/

namespace Artform

open Finset

/-- **Theorem 5.44** (Hall; supplies and demands). Let finitely many stores
hold goods `s(u) ≥ 0` and finitely many shops need goods `d(y) ≥ 0`, with equal
totals, and let each store be allowed to supply some of the shops. All the
goods can be sent along allowed pairs, every need met, if and only if every set
`U` of stores holds at most what the shops it may supply need together. Goods
are counted in whole units, as the tokens of a weave are. -/
@[book "thm:hall"]
theorem hall : Statement.hall := by
  classical
  intro Stores Shops _ _ s d allowed htot
  constructor
  · -- The condition is needed: the goods of `U` go only to the shops `U` may supply.
    rintro ⟨x, hx, hrow, hcol⟩ U
    set N := univ.filter (fun y => ∃ u ∈ U, allowed u y)
    calc ∑ u ∈ U, s u = ∑ u ∈ U, ∑ y ∈ N, x u y := by
          refine sum_congr rfl fun u hu => ?_
          rw [← hrow u]
          refine (sum_subset (subset_univ N) fun y _ hy => ?_).symm
          by_contra h
          exact hy (mem_filter.2 ⟨mem_univ y, u, hu, hx u y h⟩)
      _ = ∑ y ∈ N, ∑ u ∈ U, x u y := sum_comm
      _ ≤ ∑ y ∈ N, ∑ u, x u y := sum_le_sum fun y _ => sum_le_sum_of_subset (subset_univ U)
      _ = ∑ y ∈ N, d y := sum_congr rfl fun y _ => hcol y
  · intro hU
    -- Hall's condition for the units: a set `A` of units of goods lies over the set
    -- `U` of their stores, and the units of need they may go to are those of the shops
    -- that `U` may supply.
    have hunits : ∀ A : Finset (Σ u, Fin (s u)),
        #A ≤ #{b : Σ y, Fin (d y) | ∃ a ∈ A, allowed a.1 b.1} := by
      intro A
      calc #A ≤ #((A.image Sigma.fst).sigma fun u => (univ : Finset (Fin (s u)))) := by
            refine card_le_card fun a ha => ?_
            simp only [mem_sigma, mem_image, mem_univ, and_true]
            exact ⟨a, ha, rfl⟩
        _ = ∑ u ∈ A.image Sigma.fst, s u := by simp [card_sigma]
        _ ≤ ∑ y ∈ univ.filter (fun y => ∃ u ∈ A.image Sigma.fst, allowed u y), d y := hU _
        _ = #{b : Σ y, Fin (d y) | ∃ a ∈ A, allowed a.1 b.1} := by
            have hA : ({b : Σ y, Fin (d y) | ∃ a ∈ A, allowed a.1 b.1} : Finset _) =
                (univ.filter fun y => ∃ u ∈ A.image Sigma.fst, allowed u y).sigma
                  fun y => (univ : Finset (Fin (d y))) := by
              ext b
              simp
            rw [hA, card_sigma]
            simp
    obtain ⟨f, hf, hfa⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective
      (fun (a : Σ u, Fin (s u)) (b : Σ y, Fin (d y)) => allowed a.1 b.1)).1 hunits
    -- With equal totals, the matching of the units is a bijection.
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp [htot]⟩
    -- `x(u, y)` counts the units of `u` matched to units of `y`.
    refine ⟨fun u y => ∑ i : Fin (s u), if (f ⟨u, i⟩).1 = y then 1 else 0, ?_, ?_, ?_⟩
    · intro u y hxy
      obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hxy
      have hiy : (f ⟨u, i⟩).1 = y := by
        by_contra h
        simp [h] at hi
      exact hiy ▸ hfa ⟨u, i⟩
    · intro u
      rw [sum_comm]
      simp
    · intro y
      calc ∑ u, ∑ i : Fin (s u), (if (f ⟨u, i⟩).1 = y then 1 else 0)
          = ∑ a : Σ u, Fin (s u), if (f a).1 = y then 1 else 0 :=
            (Fintype.sum_sigma fun a => if (f a).1 = y then 1 else 0).symm
        _ = ∑ b : Σ y, Fin (d y), if b.1 = y then 1 else 0 :=
            (Equiv.ofBijective f hbij).sum_comp fun b => if b.1 = y then 1 else 0
        _ = ∑ y', ∑ _ : Fin (d y'), if y' = y then 1 else 0 :=
            Fintype.sum_sigma fun b : Σ y, Fin (d y) => if b.1 = y then 1 else 0
        _ = d y := by simp

/-! ## Non-vacuity -/

/-- The book's running example: the first tick of the queue on the square, from
`x = (1, 1, 1, 0)` to `x' = (1, 1, 0, 1)`. The stores are the corners of `x`
with their tokens, the shops the corners of `x'`, and a corner `u` may supply a
corner `y` when `u` lies in the halo of `y`: the corner behind `y`, `y` itself
or the corner ahead. The totals are three and three, every set of corners holds
at most what the corners it may supply need, and so the tick has a weave. -/
example : ∃ w : Fin 4 → Fin 4 → ℕ, (∀ u y, w u y ≠ 0 → u = y - 1 ∨ u = y ∨ u = y + 1) ∧
    (∀ u, ∑ y, w u y = ![1, 1, 1, 0] u) ∧ (∀ y, ∑ u, w u y = ![1, 1, 0, 1] y) := by
  refine (hall (Fin 4) (Fin 4) ![1, 1, 1, 0] ![1, 1, 0, 1]
    (fun u y => u = y - 1 ∨ u = y ∨ u = y + 1) (by decide)).2 fun U => ?_
  have key : ∀ U : Finset (Fin 4), ∑ u ∈ U, ![1, 1, 1, 0] u ≤
      ∑ y ∈ univ.filter (fun y => ∃ u ∈ U, u = y - 1 ∨ u = y ∨ u = y + 1), ![1, 1, 0, 1] y := by
    decide
  convert key U

end Artform
