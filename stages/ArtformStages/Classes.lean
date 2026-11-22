import ArtformStages.Incidence

/-!
# One number for each class of squares

Finding 421 of the research ledger on a layered universe proved that on a wide board a kick of
reach 1 that adds, is blind to a change at a corner, keeps Gauss's law and is one rule is
`Cᵀ diag K C` with `K` the same on each class of squares; finding 439 shows that each such `K`
is one rule, and here that two different `K` give two different kicks, so that the count of
numbers is the number of classes.

* `kick_injective` (RC2): for a table `C` from the lines to the squares whose image holds the
  difference `e σ - e τ` of every two squares, on at least three squares, `K ↦ Cᵀ diag K C` is
  injective.
-/

open Matrix

namespace Artform.Stages

/-- RC2. Where the image of `C` holds `e σ - e τ` for every two squares, and there are at least
three squares, two different numbers `K` on the squares give two different kicks `Cᵀ diag K C`. -/
theorem kick_injective {f e R : Type*} [Fintype f] [Fintype e] [DecidableEq f] [CommRing R]
    (C : Matrix f e R) (hC : ∀ σ τ : f, ∃ A : e → R, C *ᵥ A = Pi.single σ 1 - Pi.single τ 1)
    (h3 : 2 < Fintype.card f) {K K' : f → R}
    (h : Cᵀ * diagonal K * C = Cᵀ * diagonal K' * C) : K = K' := by
  funext σ
  -- two more squares
  obtain ⟨τ, ρ, hτ, hρ, hτρ⟩ : ∃ τ ρ : f, τ ≠ σ ∧ ρ ≠ σ ∧ τ ≠ ρ := by
    have hc : 1 < (Finset.univ.erase σ).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ σ), Finset.card_univ]
      omega
    obtain ⟨τ, hτ, ρ, hρ, hτρ⟩ := Finset.one_lt_card.mp hc
    exact ⟨τ, ρ, Finset.ne_of_mem_erase hτ, Finset.ne_of_mem_erase hρ, hτρ⟩
  obtain ⟨A, hA⟩ := hC σ τ
  obtain ⟨A', hA'⟩ := hC σ ρ
  -- read a kick between `A'` and `A`: it gives the number on `σ`
  have key : ∀ M : f → R, A' ⬝ᵥ ((Cᵀ * diagonal M * C) *ᵥ A) = M σ := by
    intro M
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hA, hA']
    simp only [dotProduct, mulVec_diagonal, Pi.sub_apply]
    rw [Finset.sum_eq_single σ]
    · simp [hτ.symm, hρ.symm]
    · intro x _ hx
      by_cases hxρ : x = ρ
      · subst hxρ
        simp [hρ, hτρ.symm]
      · simp [Pi.single_apply, hx, hxρ]
    · intro hσ
      exact absurd (Finset.mem_univ σ) hσ
  have hk := key K
  rw [h, key K'] at hk
  exact hk.symm

end Artform.Stages
