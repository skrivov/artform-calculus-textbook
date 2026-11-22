import ArtformStages.Strict

/-!
# The local tests of the window, on boards

A board is given here by its incidence `C`, a real table with a row for each square and a column
for each line, whose entries satisfy `C² = |C|` (they are `-1`, `0` or `1`) and each of whose
columns has its sizes summing to `2` (each line is a side of two squares). With a positive weight
`κ` on each square and a weight `λ ≥ 0` on each line, the window of Pair read on the squares is
the positivity of `squareTable C κ λ`, the diagonal of `4 / κ` less `C diag(λ) Cᵀ` (findings 427,
428 and 430 of the research ledger on a layered universe). With `p σ` the drift round `σ`:

* `board_local_sufficient` (BT1): `κ σ * p σ < 2` at every square makes the table positive
  definite;
* `board_local_necessary` (BT2): a positive definite table has `κ σ * p σ < 4` at every square.
-/

open Matrix

namespace Artform.Stages

section Board

variable {f e : Type*} [Fintype f] [Fintype e] [DecidableEq f] [DecidableEq e]

/-- The table on the squares of a board: the diagonal of `4 / κ` less `C diag(λ) Cᵀ`. -/
noncomputable def squareTable (C : Matrix f e ℝ) (κ : f → ℝ) (l : e → ℝ) : Matrix f f ℝ :=
  diagonal (fun σ => 4 / κ σ) - C * diagonal l * Cᵀ

omit [Fintype f] [DecidableEq f] [DecidableEq e] in
/-- The drift round a square: the sum of `λ` over its sides. -/
def roundDrift (C : Matrix f e ℝ) (l : e → ℝ) (σ : f) : ℝ := ∑ ℓ, |C σ ℓ| * l ℓ

omit [Fintype f] [DecidableEq f] [DecidableEq e] in
/-- The drift shared by two squares, with the signs of the incidence. -/
def crossDrift (C : Matrix f e ℝ) (l : e → ℝ) (σ τ : f) : ℝ := ∑ ℓ, C σ ℓ * l ℓ * C τ ℓ

omit [Fintype f] in
theorem squareTable_apply (C : Matrix f e ℝ) (κ : f → ℝ) (l : e → ℝ) (σ τ : f) :
    squareTable C κ l σ τ = (if σ = τ then 4 / κ σ else 0) - crossDrift C l σ τ := by
  rw [squareTable, Matrix.sub_apply, Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply, diagonal_apply, crossDrift]

omit [Fintype f] in
theorem squareTable_diag (C : Matrix f e ℝ) (κ : f → ℝ) (l : e → ℝ)
    (hC : ∀ σ ℓ, C σ ℓ ^ 2 = |C σ ℓ|) (σ : f) :
    squareTable C κ l σ σ = 4 / κ σ - roundDrift C l σ := by
  rw [squareTable_apply, ite_eq_left rfl]
  congr 1
  exact Finset.sum_congr rfl fun ℓ _ => by rw [← hC σ ℓ]; ring

/-- BT1. On a board, `κ σ * p σ < 2` at every square makes the table on the squares positive
definite: the local test that is enough for the window. -/
theorem board_local_sufficient (C : Matrix f e ℝ) (κ : f → ℝ) (l : e → ℝ)
    (hC : ∀ σ ℓ, C σ ℓ ^ 2 = |C σ ℓ|) (hcol : ∀ ℓ, ∑ σ, |C σ ℓ| = 2) (hκ : ∀ σ, 0 < κ σ)
    (hl : ∀ ℓ, 0 ≤ l ℓ) (h : ∀ σ, κ σ * roundDrift C l σ < 2) :
    (squareTable C κ l).PosDef := by
  refine posDef_of_rowsum _ ?_ ?_
  · ext σ τ
    rw [transpose_apply, squareTable_apply, squareTable_apply]
    have hc : crossDrift C l τ σ = crossDrift C l σ τ :=
      Finset.sum_congr rfl fun ℓ _ => by ring
    rw [hc]
    by_cases hστ : σ = τ
    · subst hστ; rfl
    · rw [ite_eq_right (Ne.symm hστ), ite_eq_right hστ]
  · intro σ
    have hp : 0 ≤ roundDrift C l σ :=
      Finset.sum_nonneg fun ℓ _ => mul_nonneg (abs_nonneg _) (hl ℓ)
    have hNσ : crossDrift C l σ σ = roundDrift C l σ :=
      Finset.sum_congr rfl fun ℓ _ => by rw [← hC σ ℓ]; ring
    have hbound : ∑ τ, |crossDrift C l σ τ| ≤ 2 * roundDrift C l σ := by
      calc ∑ τ, |crossDrift C l σ τ| ≤ ∑ τ, ∑ ℓ, |C σ ℓ| * l ℓ * |C τ ℓ| := by
            refine Finset.sum_le_sum fun τ _ => ?_
            refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl fun ℓ _ => by rw [abs_mul, abs_mul, abs_of_nonneg (hl ℓ)]
        _ = ∑ ℓ, |C σ ℓ| * l ℓ * ∑ τ, |C τ ℓ| := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]
        _ = 2 * roundDrift C l σ := by
            simp only [hcol, roundDrift, Finset.mul_sum]
            exact Finset.sum_congr rfl fun ℓ _ => by ring
    have hrow : ∑ τ, |squareTable C κ l σ τ| =
        |squareTable C κ l σ σ| + (∑ τ, |crossDrift C l σ τ| - |crossDrift C l σ σ|) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ),
        ← Finset.sum_erase_eq_sub (Finset.mem_univ σ)]
      congr 1
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [squareTable_apply, ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hτ)), zero_sub, abs_neg]
    have hκp : roundDrift C l σ * κ σ < 2 := by linarith [h σ]
    have h2 : roundDrift C l σ < 2 / κ σ := (lt_div_iff₀ (hκ σ)).mpr hκp
    have h42 : 4 / κ σ = 2 * (2 / κ σ) := by ring
    have h2pos : 0 < 2 / κ σ := div_pos two_pos (hκ σ)
    have hpos : 0 < 4 / κ σ - roundDrift C l σ := by linarith
    rw [hrow, squareTable_diag C κ l hC σ, abs_of_pos hpos, hNσ, abs_of_nonneg hp]
    linarith

omit [Fintype f] in
/-- BT2. A positive definite table on the squares has `κ σ * p σ < 4` at every square: the local
test that the window asks. -/
theorem board_local_necessary (C : Matrix f e ℝ) (κ : f → ℝ) (l : e → ℝ)
    (hC : ∀ σ ℓ, C σ ℓ ^ 2 = |C σ ℓ|) (hκ : ∀ σ, 0 < κ σ) (hP : (squareTable C κ l).PosDef)
    (σ : f) : κ σ * roundDrift C l σ < 4 := by
  have h := hP.diag_pos (i := σ)
  rw [squareTable_diag C κ l hC σ] at h
  have h4 : roundDrift C l σ * κ σ < 4 := (lt_div_iff₀ (hκ σ)).mp (by linarith)
  linarith

end Board

end Artform.Stages
