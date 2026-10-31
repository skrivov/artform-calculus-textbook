import ArtformScores.NonabelianGravity.HistoryCertificate

/-! # Complete source guards and all solutions certified by a rational congruence -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Matrix ι ι ℚ} (c : Certificate H)

def transformedSource (r : ι → ℚ) : ι → ℚ := c.forward.transpose.mulVec r

def Compatible (r : ι → ℚ) : Prop :=
  ∀ i, c.diagonal i = 0 → transformedSource c r i = 0

def solution (r free : ι → ℚ) : ι → ℚ :=
  c.forward.mulVec (fun i => if c.diagonal i = 0 then free i else
    transformedSource c r i / c.diagonal i)

lemma forward_inverse (y : ι → ℚ) : c.forward.mulVec (c.backward.mulVec y) = y := by
  rw [Matrix.mulVec_mulVec, c.right_inverse, Matrix.one_mulVec]

lemma backward_inverse (y : ι → ℚ) : c.backward.mulVec (c.forward.mulVec y) = y := by
  rw [Matrix.mulVec_mulVec, c.left_inverse, Matrix.one_mulVec]

lemma transpose_injective : Function.Injective c.forward.transpose.mulVec := by
  intro a b hab
  have h := congrArg c.backward.transpose.mulVec hab
  simpa only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, c.right_inverse,
    Matrix.transpose_one, Matrix.one_mulVec] using h

lemma transformed_equation (y : ι → ℚ) :
    (Matrix.diagonal c.diagonal).mulVec (c.backward.mulVec y) =
      c.forward.transpose.mulVec (H.mulVec y) := by
  rw [← c.congruence]
  simp only [← Matrix.mulVec_mulVec, forward_inverse]

lemma equation_iff (y r : ι → ℚ) : H.mulVec y = r ↔
    (Matrix.diagonal c.diagonal).mulVec (c.backward.mulVec y) = transformedSource c r := by
  rw [transformed_equation, transformedSource]
  exact (transpose_injective c).eq_iff.symm

lemma solution_iff (y r : ι → ℚ) : H.mulVec y = r ↔
    Compatible c r ∧ ∀ i, c.diagonal i ≠ 0 →
      c.backward.mulVec y i = transformedSource c r i / c.diagonal i := by
  rw [equation_iff c]
  simp only [Matrix.mulVec_diagonal, funext_iff]
  constructor
  · intro h
    constructor
    · intro i hi
      have hh := h i
      rw [hi, zero_mul] at hh
      exact hh.symm
    · intro i hi
      exact (eq_div_iff hi).mpr (by simpa [mul_comm] using h i)
  · rintro ⟨hc, hy⟩ i
    by_cases hi : c.diagonal i = 0
    · rw [hi, zero_mul, hc i hi]
    · rw [hy i hi]
      field_simp

lemma solution_valid (r free : ι → ℚ) (hr : Compatible c r) :
    H.mulVec (solution c r free) = r := by
  apply (solution_iff c _ _).mpr
  refine ⟨hr, ?_⟩
  intro i hi
  simp only [solution, backward_inverse]
  simp [hi]

lemma solution_complete (y r : ι → ℚ) (hy : H.mulVec y = r) :
    y = solution c r (c.backward.mulVec y) := by
  have h := (solution_iff c y r).mp hy
  rw [solution]
  conv_lhs => rw [← forward_inverse c y]
  congr 1
  funext i
  by_cases hi : c.diagonal i = 0
  · simp [hi]
  · simp [hi, h.2 i hi]

lemma solvable_iff (r : ι → ℚ) : (∃ y, H.mulVec y = r) ↔ Compatible c r := by
  constructor
  · rintro ⟨y, hy⟩
    exact ((solution_iff c y r).mp hy).1
  · intro hr
    exact ⟨solution c r 0, solution_valid c r 0 hr⟩

end Artform.Scores.NonabelianGravity.HistoryElimination
