import ArtformScores.GravityBridge.Native.R2ExceptionStatements
import ArtformScores.GravityBridge.Native.R2Trace

/-! # Exact zero-row, pivot and native common-factor cases -/

namespace Artform.Scores.GravityBridge.Native.R2

open Polynomial

lemma row_coeff_zero (R a G : ℝ) (i : Fin 4) :
    (rowPolys R a G i).coeff 0 = -6 * R * (2 - 3 * a) ^ 2 * constantSeeds R a i := by
  rw [coeff_zero_eq_eval_zero, rowPolys_eval]
  fin_cases i <;> dsimp [rows, rowExpr, constantSeeds] <;> ring

lemma constant_factor (R a G : ℝ) (i : Fin 4) :
    remainderConst a G (rowPolys R a G i) =
      (2 - 3 * a) ^ 2 * constantQuotient R a G i := by
  dsimp [remainderConst, constantQuotient]
  rw [row_coeff_zero]
  ring

lemma exceptional_normal (G s : ℝ) :
    normal (2 / 3 : ℝ) G s = 0 ↔ s = 0 ∨ s = 1 / 3 - 6 * G := by
  have hid : normal (2 / 3 : ℝ) G s = s * (s - (1 / 3 - 6 * G)) := by
    dsimp [normal]
    ring
  rw [hid, mul_eq_zero, sub_eq_zero]

lemma nonzero_b_on_large_normal (a G s : ℝ) (hN : normal a G s = 0)
    (hG : 0 ≤ G) (hs : 1 / 3 < s) : 2 - 3 * a ≠ 0 := by
  intro hb
  have ha : a = 2 / 3 := by linarith
  rw [ha, exceptional_normal] at hN
  rcases hN with hN | hN
  · linarith
  · linarith

lemma constant_zero_iff (R a G : ℝ) (hb : 2 - 3 * a ≠ 0) (i : Fin 4) :
    remainderConst a G (rowPolys R a G i) = 0 ↔ constantQuotient R a G i = 0 := by
  rw [constant_factor, mul_eq_zero]
  exact or_iff_right (pow_ne_zero 2 hb)

lemma zero_row_case (l n : Fin 4 → ℝ) (hl : ∀ i, l i = 0) (s : ℝ) :
    (∀ i, l i * s + n i = 0) ↔ ∀ i, n i = 0 := by simp [hl]

lemma pivot_case (l n : Fin 4 → ℝ) (j : Fin 4) (hj : l j ≠ 0) (s : ℝ) :
    (∀ i, l i * s + n i = 0) ↔
      l j * s + n j = 0 ∧ ∀ i, l j * n i - l i * n j = 0 := by
  constructor
  · intro h
    refine ⟨h j, ?_⟩
    intro i
    linear_combination l j * h i - l i * h j
  · rintro ⟨hp, hm⟩ i
    have hz : l j * (l i * s + n i) = 0 := by
      linear_combination l i * hp + hm i
    exact (mul_eq_zero.mp hz).resolve_left hj

lemma native_latitude_filter (l n : Fin 4 → ℝ) (Pi Lambda s : ℝ)
    (hL : Lambda ≠ 0) (hs : Lambda * s = Pi) :
    (∀ i, l i * s + n i = 0) ↔ ∀ i, Pi * l i + Lambda * n i = 0 := by
  constructor
  · intro h i
    linear_combination Lambda * h i - l i * hs
  · intro h i
    have hz : Lambda * (l i * s + n i) = 0 := by
      linear_combination h i + l i * hs
    exact (mul_eq_zero.mp hz).resolve_left hL

/-- **GAC:r2-exception-cases** (no affine or common-factor zero case is discarded). -/
@[ledger "GAC:r2-exception-cases"]
theorem exceptionCases : Statement.exceptionCases :=
  ⟨constant_factor, exceptional_normal, nonzero_b_on_large_normal, constant_zero_iff,
    zero_row_case, pivot_case, native_latitude_filter⟩

/-! ## Non-vacuity -/

example : normal (1 : ℝ) (1 / 36) (3 / 2) = 0 ∧
    (0 : ℝ) ≤ 1 / 36 ∧ (1 / 3 : ℝ) < 3 / 2 ∧ (2 - 3 * (1 : ℝ)) ≠ 0 := by
  norm_num [normal]

example : ∀ s : ℝ, (∀ i : Fin 4, (0 : Fin 4 → ℝ) i * s + (0 : Fin 4 → ℝ) i = 0) :=
  by simp

example :
    (![1, 2, 0, 0] : Fin 4 → ℝ) 0 ≠ 0 ∧
    ∀ i : Fin 4, (![1, 2, 0, 0] : Fin 4 → ℝ) i * 3 + ![-3, -6, 0, 0] i = 0 := by
  constructor
  · norm_num
  · intro i
    fin_cases i <;> norm_num

end Artform.Scores.GravityBridge.Native.R2
