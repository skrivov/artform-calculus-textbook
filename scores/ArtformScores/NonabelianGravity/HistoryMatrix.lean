import ArtformScores.NonabelianGravity.BoundaryHistoryKernel

/-! # The complete native forty-coordinate matrix for every finite history -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
open Legendre

abbrev Index (n : ℕ) := Fin n × Fin 40
abbrev Vector (n : ℕ) := Index n → ℚ

def row {n : ℕ} (y : Vector n) (t : Fin n) : Point ℚ := fun i => y (t, i)

def previous {n : ℕ} (x : Point ℚ) (y : Vector n) (t : Fin n) : Point ℚ :=
  if h : 0 < t.val then row y ⟨t.val - 1, by omega⟩ else x

def following {n : ℕ} (z : Point ℚ) (y : Vector n) (t : Fin n) : Point ℚ :=
  if h : t.val + 1 < n then row y ⟨t.val + 1, h⟩ else z

def historyMatrix (n : ℕ) : Matrix (Index n) (Index n) ℚ := fun s t =>
  (if s.1 = t.1 then middleH s.2 t.2 else 0) +
  (if t.1.val = s.1.val + 1 then mixed s.2 t.2 else 0) +
  (if s.1.val = t.1.val + 1 then mixed t.2 s.2 else 0)

def sourceResidual {n : ℕ} (x z : Point ℚ) (j : Vector n) : Vector n := fun t =>
  j t - (if t.1.val = 0 then mixed.transpose.mulVec x t.2 else 0) -
    (if t.1.val + 1 = n then mixed.mulVec z t.2 else 0)

def NativeMatch {n : ℕ} (x z : Point ℚ) (j y : Vector n) : Prop :=
  ∀ t, post (previous x y t) (row y t) - pre (row y t) (following z y t) = row j t

lemma history_symmetric (n : ℕ) : (historyMatrix n).IsSymm := by
  apply Matrix.IsSymm.ext
  rintro ⟨s, i⟩ ⟨t, j⟩
  by_cases h : s = t
  · subst t
    have ha : middleH j i = middleH i j :=
      congrFun (congrFun BoundaryHistory.middle_symmetric i) j
    simp [historyMatrix, ha]
  · simp [historyMatrix, h, Ne.symm h, add_comm]

lemma sum_at_nat {n : ℕ} (f : Fin n → ℚ) (k : ℕ) :
    (∑ t, if t.val = k then f t else 0) = if h : k < n then f ⟨k, h⟩ else 0 := by
  by_cases h : k < n
  · have he (t : Fin n) : t.val = k ↔ t = ⟨k, h⟩ := by
      constructor
      · intro ht; exact Fin.ext ht
      · intro ht; exact congrArg Fin.val ht
    simp [he, h]
  · have he (t : Fin n) : t.val ≠ k := by omega
    simp [he, h]

lemma sum_previous {n : ℕ} (f : Fin n → ℚ) (t : Fin n) :
    (∑ s, if t.val = s.val + 1 then f s else 0) =
      if h : 0 < t.val then f ⟨t.val - 1, by omega⟩ else 0 := by
  by_cases h : 0 < t.val
  · have he (s : Fin n) : t.val = s.val + 1 ↔ s.val = t.val - 1 := by omega
    simp only [he]
    rw [sum_at_nat]
    simp [h, show t.val - 1 < n by omega]
  · have he (s : Fin n) : t.val ≠ s.val + 1 := by omega
    simp [he, h]

lemma matrix_row {n : ℕ} (y : Vector n) (t : Fin n) (i : Fin 40) :
    (historyMatrix n).mulVec y (t, i) =
      middleH.mulVec (row y t) i +
      (if h : t.val + 1 < n then mixed.mulVec (row y ⟨t.val + 1, h⟩) i else 0) +
      (if h : 0 < t.val then mixed.transpose.mulVec (row y ⟨t.val - 1, by omega⟩) i else 0) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, historyMatrix,
    add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [sum_at_nat, sum_previous]
  simp [row]

end Artform.Scores.NonabelianGravity.HistoryElimination
