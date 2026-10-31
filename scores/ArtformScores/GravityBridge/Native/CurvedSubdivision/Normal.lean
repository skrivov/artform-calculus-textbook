import ArtformScores.GravityBridge.Native.CurvedSubdivision.CoreBoost

/-! # Supporting original curved subdivision algebra -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40
variable {K : Type*} [Field K] [CharZero K]

def detailA (c s : K) : K := 2 * s + (1 / 101 : K) * c
def detailB (s : K) : K := (1 / 101 : K) * s
def detailD (c s : K) : K := (detailA c s) ^ 2 - (detailB s) ^ 2

def returnedC (A B R J : K) : K := (A * R - B * J) / (A ^ 2 - B ^ 2)
def returnedS (A B R J : K) : K := (A * J - B * R) / (A ^ 2 - B ^ 2)

def currentDetailForce (b c s C S j : K) : K :=
  -b * (detailA c s * S + detailB s * C) - j

def currentDetailHessian (b c s C S : K) : K :=
  -b * (detailA c s * C + detailB s * S)

def currentFineValue (b c s C S : K) : K :=
  (1 / 101 : K) * b - b * (detailA c s * C + detailB s * S)

lemma original_detail_discriminant (c s : K) (hc : c ^ 2 - s ^ 2 = 1) :
    detailD c s = 4 * s ^ 2 + (4 / 101 : K) * s * c + (1 / 101 : K) ^ 2 := by
  unfold detailD detailA detailB
  linear_combination (1 / 101 : K) ^ 2 * hc

omit [CharZero K] in
lemma returned_source_and_Hessian (A B R J : K) (hD : A ^ 2 - B ^ 2 ≠ 0) :
    A * returnedS A B R J + B * returnedC A B R J = J ∧
      A * returnedC A B R J + B * returnedS A B R J = R := by
  constructor <;> unfold returnedS returnedC <;> field_simp <;> ring

omit [CharZero K] in
lemma returned_detail_Lorentz (A B R J : K) (hD : A ^ 2 - B ^ 2 ≠ 0)
    (hR : R ^ 2 - J ^ 2 = A ^ 2 - B ^ 2) :
    (returnedC A B R J) ^ 2 - (returnedS A B R J) ^ 2 = 1 := by
  unfold returnedC returnedS
  field_simp
  linear_combination (A ^ 2 - B ^ 2) * hR

omit [CharZero K] in
lemma current_source_stationary_return (b c s R J j : K) (hD : detailD c s ≠ 0)
    (hj : b * J = -j) :
    currentDetailForce b c s (returnedC (detailA c s) (detailB s) R J)
      (returnedS (detailA c s) (detailB s) R J) j = 0 ∧
    currentDetailHessian b c s (returnedC (detailA c s) (detailB s) R J)
      (returnedS (detailA c s) (detailB s) R J) = -b * R ∧
    currentFineValue b c s (returnedC (detailA c s) (detailB s) R J)
      (returnedS (detailA c s) (detailB s) R J) = (1 / 101 : K) * b - b * R := by
  have h := returned_source_and_Hessian (detailA c s) (detailB s) R J hD
  constructor
  · dsimp only [currentDetailForce]
    rw [h.1]
    linear_combination -hj
  constructor
  · dsimp only [currentDetailHessian]
    rw [h.2]
  · dsimp only [currentFineValue]
    rw [h.2]

omit [CharZero K] in
lemma complete_detail_return_unique (A B R J C S : K) (hD : A ^ 2 - B ^ 2 ≠ 0)
    (h1 : A * S + B * C = J) (h2 : A * C + B * S = R) :
    C = returnedC A B R J ∧ S = returnedS A B R J := by
  constructor <;> dsimp only [returnedC, returnedS] <;> field_simp
  · linear_combination A * h2 - B * h1
  · linear_combination A * h1 - B * h2

/-! ## Non-vacuity -/
example : returnedC (5 : ℚ) 3 5 3 = 1 ∧ returnedS (5 : ℚ) 3 5 3 = 0 ∧
    (returnedC (5 : ℚ) 3 5 3) ^ 2 - (returnedS (5 : ℚ) 3 5 3) ^ 2 = 1 := by
  norm_num [returnedC, returnedS]
end Artform.Scores.GravityBridge.Native.CurvedSubdivision
