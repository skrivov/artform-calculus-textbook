import ArtformStages.Hodge
import ArtformStages.Coulomb
import ArtformStages.TorusJoined
import ArtformStages.Waves

/-!
# The harmonic count

Finding 459 of the research ledger on a layered universe counted the three parts of a field on the
torus. Here the harmonic fields, those with no charge and no curl, are counted on every map with
`C G = 0`, and on every closed board their number is `2 - χ` (finding 462 of the ledger):

* `harmonic_count` (EU1): their dimension, the rank of `G` and the rank of `C` add up to the number
  of lines;
* `Board.transpose_ker_iff`, `Board.incidence_rank`, `Board.gauge_rank` (EU2): on a board whose
  squares are joined, `Cᵀ ψ = 0` exactly when `ψ` is the same on every square, so `rank C + 1 = F`;
  where its corners are joined, `rank G + 1 = V`;
* `Board.harmonic_euler` (EU3): so their dimension, with `V` and `F`, adds up to `E + 2`: it is
  `2 - χ`;
* `torus_harmonic_euler` (EU4): on the torus it is `2`.
-/

open Matrix Module

namespace Artform.Stages

/-- **EU1.** On every map with `C G = 0`, the dimension of the harmonic fields, the rank of `G` and
the rank of `C` add up to the number of lines. -/
theorem harmonic_count {f e v : Type*} [Fintype e] [Fintype v] (C : Matrix f e ℝ)
    (G : Matrix e v ℝ) (hCG : C * G = 0) :
    finrank ℝ ↥(LinearMap.ker Gᵀ.mulVecLin ⊓ LinearMap.ker C.mulVecLin) + G.rank + C.rank =
      Fintype.card e := by
  have hsup : LinearMap.ker Gᵀ.mulVecLin ⊔ LinearMap.ker C.mulVecLin = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy⟩ := mul_transpose_solve Gᵀ x
    rw [transpose_transpose] at hy
    refine Submodule.mem_sup.mpr ⟨x - G *ᵥ y, ?_, G *ᵥ y, ?_, sub_add_cancel x _⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, mulVec_sub, mulVec_mulVec, hy, sub_self]
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, mulVec_mulVec, hCG, zero_mulVec]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker Gᵀ.mulVecLin)
    (LinearMap.ker C.mulVecLin)
  rw [hsup, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker Gᵀ.mulVecLin
  have h3 := LinearMap.finrank_range_add_finrank_ker C.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h2 h3
  have hG : Gᵀ.rank = G.rank := rank_transpose G
  change Gᵀ.rank + _ = _ at h2
  change C.rank + _ = _ at h3
  omega

namespace Board

variable {f e v : Type*} (B : Board f e v)

/-- **EU2.** On a board whose squares are joined, `Cᵀ ψ = 0` exactly when `ψ` is the same on every
square. -/
theorem transpose_ker_iff [Fintype f] [DecidableEq e] (hJ : B.Joined) (ψ : f → ℝ) :
    B.incidenceᵀ *ᵥ ψ = 0 ↔ ∀ σ τ, ψ σ = ψ τ := by
  constructor
  · intro h σ τ
    have step : ∀ ρ ρ', (∃ i j, B.side ρ i = B.side ρ' j) → ψ ρ = ψ ρ' := by
      rintro ρ ρ' ⟨i, j, hij⟩
      by_cases hsame : (ρ, i) = (ρ', j)
      · rw [(Prod.mk.inj hsame).1]
      · have hne := B.along_ne hij hsame
        have hz := congrFun h (B.side ρ i)
        rw [Pi.zero_apply] at hz
        cases ha : B.along ρ i
        · have hb : B.along ρ' j = true := by
            revert hne
            rw [ha]
            cases B.along ρ' j <;> simp
          rw [B.incidence_transpose_mulVec ψ hij.symm hb rfl ha] at hz
          linarith
        · have hb : B.along ρ' j = false := by
            revert hne
            rw [ha]
            cases B.along ρ' j <;> simp
          rw [B.incidence_transpose_mulVec ψ rfl ha hij.symm hb] at hz
          linarith
    induction hJ σ τ with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (step _ _ hbc)
  · intro h
    funext ℓ
    obtain ⟨⟨ρ, a⟩, -, -⟩ := B.once_each_way ℓ true
    calc (B.incidenceᵀ *ᵥ ψ) ℓ = ∑ σ, B.incidence σ ℓ * ψ ρ := by
          simp only [mulVec, dotProduct, transpose_apply]
          exact Finset.sum_congr rfl fun σ _ => by rw [h σ ρ]
      _ = 0 := by rw [← Finset.sum_mul, B.incidence_col_sum, zero_mul]

/-- **EU2.** On a board whose squares are joined, `rank C + 1 = F`. -/
theorem incidence_rank [Fintype f] [Fintype e] [DecidableEq e] [Nonempty f] (hJ : B.Joined) :
    B.incidence.rank + 1 = Fintype.card f := by
  have hker : LinearMap.ker B.incidenceᵀ.mulVecLin = Submodule.span ℝ {fun _ => (1 : ℝ)} := by
    ext ψ
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton, Matrix.mulVecLin_apply,
      B.transpose_ker_iff hJ]
    constructor
    · intro h
      obtain ⟨σ₀⟩ := ‹Nonempty f›
      exact ⟨ψ σ₀, funext fun σ => by simp [h σ σ₀]⟩
    · rintro ⟨c, rfl⟩ σ τ
      rfl
  have h1 : finrank ℝ (LinearMap.ker B.incidenceᵀ.mulVecLin) = 1 := by
    rw [hker]
    refine finrank_span_singleton fun h0 => ?_
    obtain ⟨σ₀⟩ := ‹Nonempty f›
    have := congrFun h0 σ₀
    simp at this
  have hT := LinearMap.finrank_range_add_finrank_ker B.incidenceᵀ.mulVecLin
  rw [h1, Module.finrank_fintype_fun_eq_card] at hT
  have hr : B.incidenceᵀ.rank = B.incidence.rank := rank_transpose _
  change B.incidenceᵀ.rank + 1 = _ at hT
  omega

/-- **EU2.** On a board whose corners are joined, `rank G + 1 = V`. -/
theorem gauge_rank [Fintype v] [DecidableEq v] [Nonempty v] (hJ : B.CornersJoined) :
    B.gauge.rank + 1 = Fintype.card v := by
  have hker : LinearMap.ker B.gauge.mulVecLin = Submodule.span ℝ {fun _ => (1 : ℝ)} := by
    ext φ
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton, Matrix.mulVecLin_apply]
    constructor
    · intro h
      obtain ⟨w₀⟩ := ‹Nonempty v›
      exact ⟨φ w₀, funext fun w => by simp [B.gauge_const hJ φ h w w₀]⟩
    · rintro ⟨c, rfl⟩
      funext ℓ
      rw [B.gauge_mulVec]
      simp
  have h1 : finrank ℝ (LinearMap.ker B.gauge.mulVecLin) = 1 := by
    rw [hker]
    refine finrank_span_singleton fun h0 => ?_
    obtain ⟨w₀⟩ := ‹Nonempty v›
    have := congrFun h0 w₀
    simp at this
  have hT := LinearMap.finrank_range_add_finrank_ker B.gauge.mulVecLin
  rw [h1, Module.finrank_fintype_fun_eq_card] at hT
  change B.gauge.rank + 1 = _ at hT
  exact hT

/-- **EU3.** On a board whose squares and corners are joined, the dimension of the harmonic fields,
with the numbers of corners and squares, adds up to the number of lines and `2`: it is `2 - χ`. -/
theorem harmonic_euler [Fintype f] [Fintype e] [Fintype v] [DecidableEq e] [DecidableEq v]
    [Nonempty f] [Nonempty v] (hJ : B.Joined) (hV : B.CornersJoined) :
    finrank ℝ ↥(LinearMap.ker B.gaugeᵀ.mulVecLin ⊓ LinearMap.ker B.incidence.mulVecLin) +
        Fintype.card v + Fintype.card f = Fintype.card e + 2 := by
  have h := harmonic_count B.incidence B.gauge B.incidence_mul_gauge
  have hC := B.incidence_rank hJ
  have hG := B.gauge_rank hV
  omega

end Board

variable (n m : ℕ) [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)]

/-- **EU4.** On the torus the count gives the two harmonic fields of finding 459. -/
theorem torus_harmonic_euler :
    finrank ℝ ↥(LinearMap.ker (torus n m).gaugeᵀ.mulVecLin ⊓
      LinearMap.ker (torus n m).incidence.mulVecLin) = 2 := by
  have h := (torus n m).harmonic_euler (torus_joined n m) (torus_corners_joined n m)
  simp only [Fintype.card_prod, ZMod.card, Fintype.card_fin] at h
  omega

end Artform.Stages
