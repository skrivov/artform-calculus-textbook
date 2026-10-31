import ArtformScores.GravityBridge.Native.CurvedSubdivision.AnalyticSplit

/-! # Supporting original curved subdivision algebra -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40
noncomputable section

noncomputable def incomingSlot {N : ℕ} (k : Fin (N + 1)) : Fin (N + 2) := k.castSucc
noncomputable def outgoingSlot {N : ℕ} (k : Fin (N + 1)) : Fin (N + 2) := k.succ

noncomputable def edgeVariation {N : ℕ} (k : Fin (N + 1)) (e : Fin (N + 2)) : ℝ :=
  (if e = incomingSlot k then 1 else 0) - (if e = outgoingSlot k then 1 else 0)
noncomputable def rootVariation {N : ℕ} (k : Fin (N + 1)) (e : Fin (N + 2)) : ℝ :=
  if e = outgoingSlot k then 1 else 0

noncomputable def uniformNativeDetail {N : ℕ} (k : Fin (N + 1)) (b u t : ℝ) : ℝ :=
  -b * (∑ e : Fin (N + 2), Real.sinh (u + t * edgeVariation k e))-
    (2 / 101 : ℝ) * (b / (N + 2)) * (∑ e : Fin (N + 2),
      (Real.cosh ((e.val : ℝ) * u + t * rootVariation k e) - 1))

lemma exact_interior_source_derivative {N : ℕ} (k : Fin (N + 1)) (b u : ℝ) :
    HasDerivAt (uniformNativeDetail k b u)
      (-(2 / 101 : ℝ) * (b / (N + 2)) * Real.sinh (((k.val + 1 : ℕ) : ℝ) * u)) 0 := by
  have he (e : Fin (N + 2)) :
      HasDerivAt (fun t : ℝ => Real.sinh (u + t * edgeVariation k e))
        (Real.cosh u * edgeVariation k e) 0 := by
    convert (Real.hasDerivAt_sinh (u + 0 * edgeVariation k e)).comp 0
      (((hasDerivAt_id 0).mul_const (edgeVariation k e)).const_add u) using 1 <;> simp
        [Function.comp_def]
  have hv (e : Fin (N + 2)) :
      HasDerivAt (fun t : ℝ => Real.cosh ((e.val : ℝ) * u + t * rootVariation k e) - 1)
        (Real.sinh ((e.val : ℝ) * u) * rootVariation k e) 0 := by
    convert ((Real.hasDerivAt_cosh ((e.val : ℝ) * u + 0 * rootVariation k e)).comp 0
      (((hasDerivAt_id 0).mul_const (rootVariation k e)).const_add ((e.val : ℝ) * u))).sub_const 1
      using 1 <;> simp
  have hs1 := HasDerivAt.sum (u := Finset.univ) (fun e _ => he e)
  have hs2 := HasDerivAt.sum (u := Finset.univ) (fun e _ => hv e)
  have hsum1 : (∑ e : Fin (N + 2), Real.cosh u * edgeVariation k e) = 0 := by
    simp [edgeVariation, mul_sub, mul_ite, Finset.sum_sub_distrib]
  have hsum2 : (∑ e : Fin (N + 2), Real.sinh ((e.val : ℝ) * u) * rootVariation k e) =
      Real.sinh (((k.val + 1 : ℕ) : ℝ) * u) := by
    rw [Finset.sum_eq_single (outgoingSlot k)]
    · simp [rootVariation, outgoingSlot]
    · intro e _ hne
      simp [rootVariation, hne]
    · simp
  convert (hs1.const_mul (-b)).sub (hs2.const_mul ((2 / 101 : ℝ) * (b / (N + 2)))) using 1
  · funext t
    simp [uniformNativeDetail, Finset.sum_apply]
  · rw [hsum1, hsum2]
    ring

lemma every_uniform_subdivision_has_detail_residual {N : ℕ} (k : Fin (N + 1)) (b u : ℝ)
    (hb : 0 < b) (hu : 0 < u) :
    -(2 / 101 : ℝ) * (b / (N + 2)) * Real.sinh (((k.val + 1 : ℕ) : ℝ) * u) ≠ 0 := by
  have hpos : 0 < Real.sinh (((k.val + 1 : ℕ) : ℝ) * u) := by
    apply Real.sinh_pos_iff.mpr
    positivity
  have hn : (0 : ℝ) < N + 2 := by positivity
  have h : (2 / 101 : ℝ) * (b / (N + 2)) * Real.sinh (((k.val + 1 : ℕ) : ℝ) * u) > 0 := by
    positivity
  nlinarith

/-! ## Non-vacuity -/
example : HasDerivAt (uniformNativeDetail (N := 0) 0 1 (Real.log 2))
    (-(1 / 101 : ℝ) * Real.sinh (Real.log 2)) 0 := by
  convert exact_interior_source_derivative (N := 0) 0 1 (Real.log 2) using 1
  norm_num
end
end Artform.Scores.GravityBridge.Native.CurvedSubdivision
