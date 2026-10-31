import ArtformScores.NonabelianGravity.AnalyticForm
import ArtformScores.NonabelianGravity.UnitQuaternionWitness

/-! # Nonzero analytic form on actual unit-quaternion curves

The baseline has all links and impulses equal to one. The two tangent curves
vary U0 and P0 independently through unit quaternions. This tests the actual
analytic form, rather than an arbitrary functional on formal keys. This
baseline is not asserted to be a regular point of the gauge reduction.
-/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Maurer

def tangentPair (k : Key) : ℤ := if k.1=0 ∧ k.2.1=7 then 1 else 0
set_option maxHeartbeats 4000000 in
-- Evaluate a finite integer coefficient sum, with no real-number decision procedure.
lemma tangent_baseline : value tangentPair (twiceOmega original)=2 := by decide +kernel

lemma evalWord_one (w : Word) : evalWord (fun _ => (1 : Hˣ)) w=1 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨i,b⟩
    cases b <;> simp_all [evalWord,evalLetter]

def tangent (j : ℕ) (i : ℕ) : H := if i=j then 2 • imaginaryI else 0
lemma witness_pairKey (k : Key) :
    pairKey (fun _ => 1) (tangent 0) (tangent 7) k=4*(tangentPair k : ℝ) := by
  simp only [pairKey,evalWord_one,adjoint_one,tangent]
  by_cases hx : k.1=0 <;> by_cases hy : k.2.1=7 <;>
    norm_num [hx,hy,pairing,traceH,imaginaryI,tangentPair,two_smul]

lemma value_integer_cast (a : TwoForm) :
    value (fun k => (tangentPair k : ℝ)) a=(value tangentPair a : ℤ) := by
  simp [value,Int.cast_list_sum,List.map_map,Function.comp_def]

lemma actual_baseline_value :
    twoValue (fun _ => 1) (tangent 0) (tangent 7) (twiceOmega original)=8 := by
  have he (a : TwoForm) : twoValue (fun _ => 1) (tangent 0) (tangent 7) a=
      4*value (fun k => (tangentPair k : ℝ)) a := by
    induction a with
    | nil => simp [twoValue,value]
    | cons z a ih =>
      change (z.1 : ℝ)*pairKey (fun _ => 1) (tangent 0) (tangent 7) z.2+
        twoValue (fun _ => 1) (tangent 0) (tangent 7) a=_
      rw [witness_pairKey,ih,value_cons]
      ring
  rw [he,value_integer_cast,tangent_baseline]
  norm_num

def witnessCurve (j : ℕ) (i : ℕ) (t : ℝ) : H := if i=j then cayley t else 1
lemma witnessCurve_at (j i : ℕ) : witnessCurve j i 0=1 := by simp [witnessCurve,cayley_zero]
lemma witnessCurve_norm (j i : ℕ) (t : ℝ) :
    Quaternion.normSq (witnessCurve j i t)=1 := by
  by_cases hi : i=j <;> simp [witnessCurve,hi,cayley_norm]
lemma witnessCurve_derivative (j i : ℕ) :
    HasDerivAt (witnessCurve j i) (tangent j i*(1 : H)) 0 := by
  by_cases hi : i=j
  · have he : witnessCurve j i=cayley := by funext r; simp [witnessCurve,hi]
    rw [he]
    simpa only [tangent,hi,↓reduceIte,mul_one] using cayley_derivative
  · have he : witnessCurve j i=(fun _ => (1 : H)) := by
      funext r
      simp [witnessCurve,hi]
    rw [he]
    simpa only [tangent,hi,↓reduceIte,zero_mul] using hasDerivAt_const (0:ℝ) (1:H)

lemma analytic_baseline_value :
    analyticTwiceOmega (witnessCurve 0) (witnessCurve 7) 0 original=8 := by
  rw [analyticTwiceOmega_value _ _ (fun _ => 1) (tangent 0) (tangent 7) 0
    (witnessCurve_at 0) (witnessCurve_at 7) (witnessCurve_derivative 0)
    (witnessCurve_derivative 7),actual_baseline_value]

/-! ## Non-vacuity -/
example : analyticTwiceOmega (witnessCurve 0) (witnessCurve 7) 0 original ≠ 0 := by
  rw [analytic_baseline_value]
  norm_num
end Artform.Scores.NonabelianGravity.Maurer
