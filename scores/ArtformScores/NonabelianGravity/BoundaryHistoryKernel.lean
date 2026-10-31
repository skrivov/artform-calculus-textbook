import ArtformScores.NonabelianGravity.BoundaryHistoryColumns

/-! # Exact compact Ward vectors and the extra three-cell source condition -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.BoundaryHistory
open Artform.Scores.GravityBridge.Native.Full40
open Artform.Scores.NonabelianGravity.Legendre

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Normalize the six sparse columns at all40 point coordinates.
lemma first_columns_apply (w : Biv ℚ) : firstColumns.mulVec w = gaugeFirst w := by
  funext i
  fin_cases i <;> norm_num [firstColumns, gaugeFirst, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Normalize the coframe and connection columns without expanding the dense Hessian.
lemma second_columns_apply (w : Biv ℚ) : secondColumns.mulVec w = gaugeSecond w := by
  funext i
  fin_cases i <;> norm_num [secondColumns, gaugeSecond, lie, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

lemma first_null (w : Biv ℚ) :
    middleH.mulVec (gaugeFirst w) + mixed.mulVec (gaugeSecond w) = 0 := by
  have h := congrArg (fun M => M.mulVec w) first_columns_null
  simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.zero_mulVec,
    first_columns_apply, second_columns_apply] using h

lemma second_null (w : Biv ℚ) :
    mixed.transpose.mulVec (gaugeFirst w) + middleH.mulVec (gaugeSecond w) = 0 := by
  have h := congrArg (fun M => M.mulVec w) second_columns_null
  simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.zero_mulVec,
    first_columns_apply, second_columns_apply] using h

lemma incoming_zero (w : Biv ℚ) : mixed.mulVec (gaugeFirst w) = 0 := by
  have h := congrArg (fun M => M.mulVec w) incoming_columns_zero
  simpa only [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, first_columns_apply] using h

lemma outgoing_zero (w : Biv ℚ) : mixed.transpose.mulVec (gaugeSecond w) = 0 := by
  have h := congrArg (fun M => M.mulVec w) outgoing_columns_zero
  simpa only [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, second_columns_apply] using h

lemma middle_symmetric : middleH.transpose = middleH := by
  simp only [middleH, Matrix.transpose_add, old_symmetric, new_symmetric]

def ThreeCellMatch (x y v z j₁ j₂ : Point ℚ) : Prop :=
  post x y - pre y v = j₁ ∧ post y v - pre v z = j₂

lemma source_compatibility (x y v z j₁ j₂ : Point ℚ)
    (h : ThreeCellMatch x y v z j₁ j₂) (w : Biv ℚ) :
    pair (gaugeFirst w) j₁ + pair (gaugeSecond w) j₂ = 0 := by
  have h₁ := (matching_iff x y v j₁).mp h.1
  have h₂ := (matching_iff y v z j₂).mp h.2
  have hj₁ : j₁ = middleH.mulVec y + mixed.transpose.mulVec x + mixed.mulVec v := by
    linear_combination -h₁
  have hj₂ : j₂ = middleH.mulVec v + mixed.transpose.mulVec y + mixed.mulVec z := by
    linear_combination -h₂
  have sym (g t : Point ℚ) : pair g (middleH.mulVec t) = pair (middleH.mulVec g) t := by
    rw [← middle_symmetric, transpose_pair, middle_symmetric]
  have tr (g t : Point ℚ) : pair g (mixed.mulVec t) =
      pair (mixed.transpose.mulVec g) t := (transpose_pair mixed g t).symm
  have tt (g t : Point ℚ) : pair g (mixed.transpose.mulVec t) =
      pair (mixed.mulVec g) t := by
    rw [← transpose_pair mixed.transpose g t, Matrix.transpose_transpose]
  rw [hj₁, hj₂]
  simp only [pair, dotProduct_add]
  change pair (gaugeFirst w) (middleH.mulVec y) +
      pair (gaugeFirst w) (mixed.transpose.mulVec x) + pair (gaugeFirst w) (mixed.mulVec v) +
    (pair (gaugeSecond w) (middleH.mulVec v) +
      pair (gaugeSecond w) (mixed.transpose.mulVec y) + pair (gaugeSecond w) (mixed.mulVec z)) = 0
  rw [sym, sym, tr, tr, tt, tt, incoming_zero, outgoing_zero]
  have hn₁ := congrArg (fun q => pair q y) (first_null w)
  have hn₂ := congrArg (fun q => pair q v) (second_null w)
  simp only [pair, add_dotProduct, zero_dotProduct] at hn₁ hn₂ ⊢
  linear_combination hn₁ + hn₂

def source16 : Point ℚ := fun i => if i = 16 then 1 else 0

def boost01 : Biv ℚ := fun i => if i = 0 then 1 else 0

lemma source16_active : activeProjector.mulVec source16 = source16 := by decide +kernel

lemma source16_rejected (x z : Point ℚ) :
    ¬ ∃ y v, ThreeCellMatch x y v z source16 0 := by
  rintro ⟨y, v, h⟩
  have hc := source_compatibility x y v z source16 0 h boost01
  norm_num [pair, gaugeFirst, source16, boost01, dotProduct, Fin.sum_univ_succ] at hc

lemma zero_three_cell : ThreeCellMatch 0 0 0 0 0 0 := ⟨zero_matching, zero_matching⟩

end Artform.Scores.NonabelianGravity.BoundaryHistory
