import ArtformStages.Hodge

/-!
# The Coulomb gauge

For a map `C` from the lines to the squares and a gauge `G` with `C G = 0`, as on every board and
in every closed solid, the gauge of a potential can be fixed, and fixed once (finding 458 of the
research ledger on a layered universe):

* `coulomb_gauge_exists` (CG1): every potential `A` has a gauge-equivalent potential `A + G φ` with
  no divergence;
* `coulomb_gauge_unique` (CG2): two gauge-equivalent potentials with no divergence are equal;
* `pair_keeps_coulomb_gauge`, `pair_iterate_keeps_coulomb_gauge` (CG3, CG4): with no charge, Pair
  with one drift keeps a potential with no divergence, step after step.
-/

open Matrix

namespace Artform.Stages

variable {f e v : Type*} [Fintype f] [Fintype e] [Fintype v]

/-- **CG1.** Every potential has a gauge-equivalent potential with no divergence. -/
theorem coulomb_gauge_exists (G : Matrix e v ℝ) (A : e → ℝ) :
    ∃ φ : v → ℝ, Gᵀ *ᵥ (A + G *ᵥ φ) = 0 := by
  obtain ⟨y, hy⟩ := mul_transpose_solve Gᵀ A
  rw [transpose_transpose] at hy
  refine ⟨-y, ?_⟩
  rw [mulVec_add, mulVec_neg, mulVec_neg, mulVec_mulVec, hy, add_neg_cancel]

/-- **CG2.** Two gauge-equivalent potentials with no divergence are equal. -/
theorem coulomb_gauge_unique (G : Matrix e v ℝ) (A : e → ℝ) (φ φ' : v → ℝ)
    (h : Gᵀ *ᵥ (A + G *ᵥ φ) = 0) (h' : Gᵀ *ᵥ (A + G *ᵥ φ') = 0) :
    A + G *ᵥ φ = A + G *ᵥ φ' := by
  have hd : Gᵀ *ᵥ (G *ᵥ (φ - φ')) = 0 := by
    have e1 : G *ᵥ (φ - φ') = (A + G *ᵥ φ) - (A + G *ᵥ φ') := by
      rw [mulVec_sub]
      abel
    rw [e1, mulVec_sub, h, h', sub_zero]
  have hz : (G *ᵥ (φ - φ')) ⬝ᵥ (G *ᵥ (φ - φ')) = 0 := by
    rw [dotProduct_mulVec_left, hd, zero_dotProduct]
  have h0 : G *ᵥ (φ - φ') = 0 := dotProduct_self_eq_zero.mp hz
  rw [mulVec_sub, sub_eq_zero] at h0
  rw [h0]

variable [DecidableEq e]

omit [Fintype v] in
/-- **CG3.** With no charge, a step of Pair with every kick `Cᵀ K C` and one drift `λ` keeps a
potential with no divergence, and keeps `E` with no charge. -/
theorem pair_keeps_coulomb_gauge (C : Matrix f e ℝ) (G : Matrix e v ℝ) (hCG : C * G = 0)
    (K : Matrix f f ℝ) (l : ℝ) (x : LightState ℝ e) (hA : Gᵀ *ᵥ x.1 = 0) (hE : Gᵀ *ᵥ x.2 = 0) :
    Gᵀ *ᵥ (pair (Cᵀ * K * C) (diagonal fun _ : e => l) x).1 = 0 ∧
      Gᵀ *ᵥ (pair (Cᵀ * K * C) (diagonal fun _ : e => l) x).2 = 0 := by
  have hGC : Gᵀ * Cᵀ = 0 := by rw [← transpose_mul, hCG, transpose_zero]
  have hE' : Gᵀ *ᵥ (x.2 + (Cᵀ * K * C) *ᵥ x.1) = 0 := by
    rw [mulVec_add, hE, zero_add, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec, hGC,
      zero_mulVec]
  have hD : ∀ u : e → ℝ, (diagonal fun _ : e => l) *ᵥ u = l • u := by
    intro u
    funext ℓ
    simp [mulVec_diagonal]
  simp only [pair]
  refine ⟨?_, hE'⟩
  rw [hD, mulVec_sub, mulVec_smul, hE', smul_zero, hA, sub_zero]

omit [Fintype v] in
/-- **CG4.** So every number of steps keeps them. -/
theorem pair_iterate_keeps_coulomb_gauge (C : Matrix f e ℝ) (G : Matrix e v ℝ) (hCG : C * G = 0)
    (K : Matrix f f ℝ) (l : ℝ) (x : LightState ℝ e) (hA : Gᵀ *ᵥ x.1 = 0) (hE : Gᵀ *ᵥ x.2 = 0)
    (k : ℕ) :
    Gᵀ *ᵥ ((pair (Cᵀ * K * C) (diagonal fun _ : e => l))^[k] x).1 = 0 ∧
      Gᵀ *ᵥ ((pair (Cᵀ * K * C) (diagonal fun _ : e => l))^[k] x).2 = 0 := by
  induction k generalizing x with
  | zero => exact ⟨hA, hE⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2⟩ := pair_keeps_coulomb_gauge C G hCG K l x hA hE
    exact ih _ h1 h2

end Artform.Stages
