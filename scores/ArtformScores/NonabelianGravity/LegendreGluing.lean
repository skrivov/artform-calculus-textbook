import ArtformScores.NonabelianGravity.LegendreVariation
import ArtformScores.NonabelianGravity.LegendreComposition

/-! # Source compatibility and a concrete failure of one-cell extension -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Legendre

lemma projector_rank : Matrix.rank activeProjector = 36 := by
  have hd : activeProjector = Matrix.diagonal (fun i : Fin 40 =>
      if i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 8 ∧ i ≠ 12 then (1 : ℚ) else 0) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [activeProjector]
    · simp [activeProjector, h]
  rw [hd, Matrix.rank_diagonal]
  decide +kernel

lemma middle_rank : Matrix.rank middleH = 36 := by
  rw [← projector_rank]
  apply le_antisymm
  · calc
      Matrix.rank middleH = Matrix.rank (activeProjector * middleH) := by rw [middle_active]
      _ ≤ Matrix.rank activeProjector := Matrix.rank_mul_le_left _ _
  · calc
      Matrix.rank activeProjector = Matrix.rank (middleH * middleInverse) := by
        rw [middle_inverse_right]
      _ ≤ Matrix.rank middleH := Matrix.rank_mul_le_left _ _

lemma castMatrix_rat (M : Matrix (Fin 40) (Fin 40) ℚ) : castMatrix M = M := by
  ext i j
  simp [castMatrix]

lemma matching_iff (x y z j : Point ℚ) : post x y - pre y z = j ↔
    middleH.mulVec y = j - mixed.transpose.mulVec x - mixed.mulVec z := by
  simp only [post, pre, castMatrix_rat, middleH, Matrix.add_mulVec]
  constructor <;> intro h <;> linear_combination h

lemma middle_solution (r y : Point ℚ) : middleH.mulVec y = r ↔
    activeProjector.mulVec r = r ∧ activeProjector.mulVec y = middleInverse.mulVec r := by
  constructor
  · intro h
    constructor
    · rw [← h, Matrix.mulVec_mulVec, middle_active, h]
    · rw [← h, Matrix.mulVec_mulVec, middle_inverse_left]
  · rintro ⟨hr, hy⟩
    calc
      middleH.mulVec y = middleH.mulVec (activeProjector.mulVec y) := by
        rw [Matrix.mulVec_mulVec, middle_active_right]
      _ = middleH.mulVec (middleInverse.mulVec r) := by rw [hy]
      _ = r := by rw [Matrix.mulVec_mulVec, middle_inverse_right, hr]

def residual (x z j : Point ℚ) : Point ℚ :=
  j - mixed.transpose.mulVec x - mixed.mulVec z

lemma compatibility_iff (x z j : Point ℚ) :
    activeProjector.mulVec (residual x z j) = residual x z j ↔
      activeProjector.mulVec j = j := by
  simp only [residual, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    active_mixed_transpose, active_mixed]
  constructor <;> intro h <;> linear_combination h

lemma matching_solution (x y z j : Point ℚ) : post x y - pre y z = j ↔
    activeProjector.mulVec j = j ∧
      activeProjector.mulVec y = middleInverse.mulVec (residual x z j) := by
  rw [matching_iff, middle_solution]
  exact and_congr_left (fun _ => compatibility_iff x z j)

def unit25 : Point ℚ := fun i => if i = 25 then 1 else 0
def flatMomentum : Point ℚ := fun i => -background i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- A nonzero endpoint is genuinely admitted by the complete one-cell relation.
lemma admitted_unit : NativeRelation ((0 : Point ℚ), flatMomentum) (unit25, flatMomentum) := by
  unfold NativeRelation
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Normalize the full forty-coordinate row, leaving the next endpoint arbitrary.
lemma pre_unit25 (z : Point ℚ) : pre unit25 z 25 = -4 / 101 := by
  norm_num [pre, castMatrix, oldH, mixed, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, unit25, background]

lemma unit_nonextension : ¬ ∃ b : Phase ℚ, NativeRelation (unit25, flatMomentum) b := by
  rintro ⟨b, hp, _⟩
  have h := congrFun hp 25
  rw [pre_unit25] at h
  norm_num [flatMomentum, background] at h

lemma unit_nonzero : unit25 ≠ 0 := by
  intro h
  have h25 := congrFun h 25
  norm_num [unit25] at h25

def unit0 : Point ℚ := fun i => if i = 0 then 1 else 0

lemma inactive_source_rejected : ¬ ∃ y : Point ℚ,
    post 0 y - pre y 0 = unit0 := by
  rintro ⟨y, hy⟩
  have hc := (matching_solution 0 y 0 unit0).mp hy
  have h0 := congrFun hc.1 0
  norm_num [activeProjector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, unit0] at h0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Exact zero-field matching supplies a nonempty composable case.
lemma zero_matching : post (0 : Point ℚ) 0 - pre 0 0 = 0 := by decide +kernel

end Artform.Scores.NonabelianGravity.Legendre
