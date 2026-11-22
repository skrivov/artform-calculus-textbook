import ArtformStages.Dual

/-!
# The strict window, and diagonal dominance

Finding 428 of the research ledger on a layered universe reads the window of Pair on the squares
and gives it a local test; two of its steps were recalled, not proved. Here they are theorems.

* `window_dual_strict` (SD1): for positive definite `A` and `D`, `D - Bᴴ A⁻¹ B` is positive
  definite exactly when `A - B D⁻¹ Bᴴ` is: the open window on the lines is the open window on the
  squares.
* `posDef_of_rowsum` (SD2): a real symmetric table each of whose rows has its sizes summing to less
  than twice its diagonal entry is positive definite: the local test of the window.
-/

open Matrix
open scoped ComplexOrder

namespace Artform.Stages

section Strict

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- SD1. The strict form of `window_dual`. -/
theorem window_dual_strict {A : Matrix m m 𝕜} {D : Matrix n n 𝕜} (B : Matrix m n 𝕜)
    (hA : A.PosDef) (hD : D.PosDef) [Invertible A] [Invertible D] :
    (D - Bᴴ * A⁻¹ * B).PosDef ↔ (A - B * D⁻¹ * Bᴴ).PosDef := by
  have h1 := det_fromBlocks₁₁ A B Bᴴ D
  have h2 := det_fromBlocks₂₂ A B Bᴴ D
  rw [invOf_eq_nonsing_inv] at h1 h2
  have hA0 : A.det ≠ 0 := (isUnit_det_of_invertible A).ne_zero
  have hD0 : D.det ≠ 0 := (isUnit_det_of_invertible D).ne_zero
  have hdet : (D - Bᴴ * A⁻¹ * B).det ≠ 0 ↔ (A - B * D⁻¹ * Bᴴ).det ≠ 0 := by
    constructor
    · intro h h'
      apply h
      have : A.det * (D - Bᴴ * A⁻¹ * B).det = 0 := by rw [← h1, h2, h', mul_zero]
      exact (mul_eq_zero.mp this).resolve_left hA0
    · intro h h'
      apply h
      have : D.det * (A - B * D⁻¹ * Bᴴ).det = 0 := by rw [← h2, h1, h', mul_zero]
      exact (mul_eq_zero.mp this).resolve_left hD0
  constructor
  · intro h
    exact ((window_dual B hA hD).mp h.posSemidef).posDef_iff_det_ne_zero.mpr
      (hdet.mp (h.posSemidef.posDef_iff_det_ne_zero.mp h))
  · intro h
    exact ((window_dual B hA hD).mpr h.posSemidef).posDef_iff_det_ne_zero.mpr
      (hdet.mpr (h.posSemidef.posDef_iff_det_ne_zero.mp h))

end Strict

section Dominance

variable {n : Type*} [Fintype n]

/-- SD2. A real symmetric table each of whose rows has its sizes summing to less than twice its
diagonal entry is positive definite. -/
theorem posDef_of_rowsum (M : Matrix n n ℝ) (hM : Mᵀ = M) (h : ∀ i, ∑ j, |M i j| < 2 * M i i) :
    M.PosDef := by
  have hsym : ∀ i j, M j i = M i j := fun i j => by
    simpa [transpose_apply] using congrFun (congrFun hM i) j
  have hH : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hM]
  refine PosDef.of_dotProduct_mulVec_pos hH fun v hv => ?_
  rw [star_trivial]
  have hterm : ∀ i j, 0 ≤ M i j * (v i * v j) + |M i j| * (v i ^ 2 + v j ^ 2) / 2 := by
    intro i j
    rcases le_total 0 (M i j) with hm | hm
    · rw [abs_of_nonneg hm]; nlinarith [sq_nonneg (v i + v j)]
    · rw [abs_of_nonpos hm]; nlinarith [sq_nonneg (v i - v j)]
  have hdiag : ∀ i, 0 < M i i := fun i => by
    have h1 : |M i i| ≤ ∑ j, |M i j| :=
      Finset.single_le_sum (f := fun j => |M i j|) (fun j _ => abs_nonneg (M i j))
        (Finset.mem_univ i)
    linarith [h i, neg_abs_le (M i i)]
  have hq : v ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ j, M i j * (v i * v j) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have htotal : v ⬝ᵥ (M *ᵥ v) =
      ∑ i, ∑ j, (M i j * (v i * v j) + |M i j| * (v i ^ 2 + v j ^ 2) / 2) -
        ∑ i, ∑ j, |M i j| * (v i ^ 2 + v j ^ 2) / 2 := by
    rw [hq, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_sub_distrib]; simp
  have hfirst : ∑ i, 2 * M i i * v i ^ 2 ≤
      ∑ i, ∑ j, (M i j * (v i * v j) + |M i j| * (v i ^ 2 + v j ^ 2) / 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := Finset.single_le_sum
      (f := fun j => M i j * (v i * v j) + |M i j| * (v i ^ 2 + v j ^ 2) / 2)
      (fun j _ => hterm i j) (Finset.mem_univ i)
    rw [abs_of_pos (hdiag i)] at this
    nlinarith [this]
  have s1 : ∑ i, ∑ j, |M i j| * v i ^ 2 = ∑ i, (∑ j, |M i j|) * v i ^ 2 := by
    simp only [Finset.sum_mul]
  have s2 : ∑ i, ∑ j, |M i j| * v j ^ 2 = ∑ i, (∑ j, |M i j|) * v i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by rw [hsym a b]
  have hsecond : ∑ i, ∑ j, |M i j| * (v i ^ 2 + v j ^ 2) / 2 =
      ∑ i, (∑ j, |M i j|) * v i ^ 2 := by
    have e : ∀ i j, |M i j| * (v i ^ 2 + v j ^ 2) / 2 =
        |M i j| * v i ^ 2 / 2 + |M i j| * v j ^ 2 / 2 := fun i j => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [s1, s2]
    ring
  have hsplit : ∑ i, (2 * M i i - ∑ j, |M i j|) * v i ^ 2 =
      ∑ i, 2 * M i i * v i ^ 2 - ∑ i, (∑ j, |M i j|) * v i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpos : 0 < ∑ i, (2 * M i i - ∑ j, |M i j|) * v i ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv (funext hc)
    refine Finset.sum_pos' (fun i _ => mul_nonneg (by linarith [h i]) (sq_nonneg _)) ?_
    exact ⟨k, Finset.mem_univ k, mul_pos (by linarith [h k])
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk)))⟩
  linarith [htotal, hfirst, hsecond, hsplit, hpos]

end Dominance

end Artform.Stages
