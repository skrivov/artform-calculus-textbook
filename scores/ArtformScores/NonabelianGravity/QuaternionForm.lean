import ArtformScores.NonabelianGravity.Differential
import Mathlib.Analysis.Quaternion

/-! # Actual quaternion pairing semantics for the formal exterior certificates

The pairing is minus the real part of a product. On imaginary quaternions it
is the positive Euclidean pairing. Its conjugation invariance is proved here;
it is not an extra hypothesis on the finite word normalizer.
-/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Maurer
abbrev H := Quaternion ℝ

def traceH : H →+ ℝ where
  toFun q := -q.re
  map_zero' := by simp
  map_add' a b := by
    change -(a.re+b.re) = -a.re + -b.re
    ring
def pairing (a b : H) : ℝ := traceH (a*b)

lemma trace_cycle (a b : H) : traceH (a*b)=traceH (b*a) := by
  dsimp [traceH]
  ring
lemma trace_adjoint (u : Hˣ) (a : H) : traceH (adjoint u a)=traceH a := by
  rw [adjoint,trace_cycle]
  simp
lemma pairing_adjoint (u : Hˣ) (a b : H) :
    pairing (adjoint u a) (adjoint u b)=pairing a b := by
  unfold pairing
  have he : adjoint u a*adjoint u b=adjoint u (a*b) := by simp [adjoint,mul_assoc]
  rw [he,trace_adjoint]
lemma pairing_move (u v : Hˣ) (a b : H) :
    pairing (adjoint u a) (adjoint v b)=pairing a (adjoint (u⁻¹*v) b) := by
  have he := pairing_adjoint u⁻¹ (adjoint u a) (adjoint v b)
  simpa only [← adjoint_mul,inv_mul_cancel,adjoint_one] using he.symm
lemma pairing_add_left (a b c : H) : pairing (a+b) c=pairing a c+pairing b c := by
  simp [pairing,add_mul]
lemma pairing_add_right (a b c : H) : pairing a (b+c)=pairing a b+pairing a c := by
  simp [pairing,mul_add]
lemma pairing_zsmul_left (n : ℤ) (a b : H) : pairing (n • a) b=(n : ℝ)*pairing a b := by
  unfold pairing
  rw [show (n • a)*b=n • (a*b) from (AddMonoidHom.mulRight b).map_zsmul n a,
    map_zsmul,zsmul_eq_mul]
lemma pairing_zsmul_right (n : ℤ) (a b : H) : pairing a (n • b)=(n : ℝ)*pairing a b := by
  unfold pairing
  rw [show a*(n • b)=n • (a*b) from (AddMonoidHom.mulLeft a).map_zsmul n b,
    map_zsmul,zsmul_eq_mul]
@[simp] lemma pairing_zero_left (a : H) : pairing 0 a=0 := by simp [pairing]
@[simp] lemma pairing_zero_right (a : H) : pairing a 0=0 := by simp [pairing]

def pairKey (g : ℕ → Hˣ) (x y : ℕ → H) (k : Key) : ℝ :=
  pairing (x k.1) (adjoint (evalWord g k.2.2) (y k.2.1))
def twoValue (g : ℕ → Hˣ) (x y : ℕ → H) (a : TwoForm) : ℝ := value (pairKey g x y) a
lemma twoValue_append (g : ℕ → Hˣ) (x y : ℕ → H) (a b : TwoForm) :
    twoValue g x y (a++b)=twoValue g x y a+twoValue g x y b := by
  simp [twoValue,value]
lemma twoValue_negative (g : ℕ → Hˣ) (x y : ℕ → H) (a : TwoForm) :
    twoValue g x y (negative a) = -twoValue g x y a := by
  induction a with
  | nil => simp [twoValue,value,negative]
  | cons t a ih =>
    simp only [negative,List.map_cons,twoValue,value_cons,Int.cast_neg,neg_mul] at ih ⊢
    rw [ih]
    ring

lemma pairing_one_left (g : ℕ → Hˣ) (x : ℕ → H) (a : OneForm) (b : H) :
    pairing (oneValue g x a) b=
      (a.map fun t => (t.1 : ℝ)*pairing (adjoint (evalWord g t.2.2) (x t.2.1)) b).sum := by
  induction a with
  | nil => simp
  | cons t a ih => simp only [oneValue_cons,pairing_add_left,pairing_zsmul_left,ih,List.map_cons,
      List.sum_cons]
lemma pairing_one_right (g : ℕ → Hˣ) (y : ℕ → H) (a : H) (b : OneForm) :
    pairing a (oneValue g y b)=
      (b.map fun t => (t.1 : ℝ)*pairing a (adjoint (evalWord g t.2.2) (y t.2.1))).sum := by
  induction b with
  | nil => simp
  | cons t b ih => simp only [oneValue_cons,pairing_add_right,pairing_zsmul_right,ih,List.map_cons,
      List.sum_cons]

lemma twoValue_wedge (g : ℕ → Hˣ) (x y : ℕ → H) (a b : OneForm) :
    twoValue g x y (wedge a b)=
      pairing (oneValue g x a) (oneValue g y b)-
        pairing (oneValue g x b) (oneValue g y a) := by
  induction a with
  | nil => simp [wedge,twoValue,value]
  | cons t a ih =>
    change twoValue g x y ((b.flatMap fun u =>
      [(t.1*u.1,t.2.1,u.2.1,wm (wi t.2.2) u.2.2),
       (-(t.1*u.1),u.2.1,t.2.1,wm (wi u.2.2) t.2.2)])++wedge a b)=_
    rw [twoValue_append,ih]
    simp only [oneValue_cons,pairing_add_left,pairing_add_right,
      pairing_zsmul_left,pairing_zsmul_right]
    have ht : twoValue g x y (b.flatMap fun u =>
        [(t.1*u.1,t.2.1,u.2.1,wm (wi t.2.2) u.2.2),
        (-(t.1*u.1),u.2.1,t.2.1,wm (wi u.2.2) t.2.2)])=
        (t.1 : ℝ)*pairing (adjoint (evalWord g t.2.2) (x t.2.1)) (oneValue g y b)-
        (t.1 : ℝ)*pairing (oneValue g x b) (adjoint (evalWord g t.2.2) (y t.2.1)) := by
      clear ih
      induction b with
      | nil => simp [twoValue,value]
      | cons u b ihb =>
        simp only [List.flatMap_cons,twoValue_append,ihb,oneValue_cons,
          pairing_add_left,pairing_add_right,pairing_zsmul_left,pairing_zsmul_right]
        simp only [twoValue,value,pairKey,List.map_cons,List.map_nil,List.sum_cons,
          List.sum_nil,Int.cast_neg,Int.cast_mul,neg_mul,add_zero,eval_wm,eval_wi]
        rw [← pairing_move,← pairing_move]
        ring
    rw [ht]
    ring

/-! ## Non-vacuity -/
def imaginaryI : H := ⟨0,1,0,0⟩
example : pairing imaginaryI imaginaryI=1 := by norm_num [pairing,traceH,imaginaryI]
end Artform.Scores.NonabelianGravity.Maurer
