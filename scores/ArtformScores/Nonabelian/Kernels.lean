import ArtformScores.Nonabelian.Orbits

/-! # Orthogonal curvature and electric score kernels -/
set_option autoImplicit false
namespace Artform.Scores.Nonabelian
open Finset
def reflect : Matrix G G ℚ := fun x y => 1/3 - if x=y then 1 else 0
lemma reflect_transpose : reflect.transpose=reflect := by
  apply Matrix.ext; intro x y
  simp [reflect,eq_comm]
lemma reflect_square : reflect*reflect=1 := by
  apply Matrix.ext
  intro x y
  simp only [Matrix.mul_apply,reflect,sub_mul,mul_sub,Finset.sum_sub_distrib]
  simp only [ite_mul,mul_ite,zero_mul,mul_zero,one_mul,mul_one]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',mem_univ,ite_true,Finset.sum_const,
    Finset.card_univ,Fintype.card_perm,Fintype.card_fin,Nat.factorial]
  by_cases h : x=y <;> simp [h,Matrix.one_apply] <;> norm_num

def electric (e : Bool) : Matrix Raw Raw ℚ :=
  if e then Matrix.kroneckerMap (· * ·) (1 : Matrix G G ℚ) reflect
  else Matrix.kroneckerMap (· * ·) reflect (1 : Matrix G G ℚ)
lemma electric_square (e : Bool) : electric e*electric e=1 := by
  cases e <;> simp only [electric,Bool.false_eq_true,ite_false,ite_true,
    ← Matrix.mul_kronecker_mul,reflect_square,Matrix.one_mul,Matrix.one_kronecker_one]
lemma electric_formula (e : Bool) (x y : Raw) : electric e x y=
    (if (if e then x.1=y.1 else x.2=y.2) then (1:ℚ)/3 else 0) -
      if x=y then 1 else 0 := by
  cases e <;> simp only [electric,Bool.false_eq_true,ite_true,ite_false,
    Matrix.kroneckerMap_apply,Matrix.one_apply,reflect]
  · by_cases h : x.2=y.2 <;> by_cases h' : x.1=y.1 <;>
      simp [h,h',Prod.ext_iff]
  · by_cases h : x.1=y.1 <;> by_cases h' : x.2=y.2 <;>
      simp [h,h',Prod.ext_iff]
lemma electric_transpose (e : Bool) : (electric e).transpose=electric e := by
  apply Matrix.ext
  intro x y
  change electric e y x=electric e x y
  rw [electric_formula,electric_formula]
  cases e <;> simp [eq_comm]

def phaseSign (active : Bool) (x : Raw) : ℚ :=
  if active then (if curvature x=1 then 1 else -1) else 1
def magnetic (active : Bool) : Matrix Raw Raw ℚ := Matrix.diagonal (phaseSign active)
lemma sign_square (active : Bool) (x : Raw) : phaseSign active x*phaseSign active x=1 := by
  unfold phaseSign; split_ifs <;> norm_num
lemma magnetic_square (active : Bool) : magnetic active*magnetic active=1 := by
  simp only [magnetic,Matrix.diagonal_mul_diagonal,sign_square,Matrix.diagonal_one]
lemma magnetic_transpose (active : Bool) : (magnetic active).transpose=magnetic active := by
  simp [magnetic]
lemma magnetic_off : magnetic false=1 := by
  change Matrix.diagonal (fun x => phaseSign false x)=1
  simp [phaseSign]

def Covariant {R : Type} (M : Matrix Raw Raw R) : Prop := ∀ h x y, M (gauge h x) (gauge h y)=M x y
lemma conjugate_eq (h a b : G) : conjugate h a=conjugate h b ↔ a=b := by
  exact (MulAut.conj h).injective.eq_iff
lemma electric_covariant (e : Bool) : Covariant (electric e) := by
  intro h x y
  rw [electric_formula,electric_formula]
  cases e <;> simp [gauge,conjugate_eq,Prod.ext_iff]
lemma phaseSign_gauge (active : Bool) (h : G) (x : Raw) :
    phaseSign active (gauge h x)=phaseSign active x := by
  have he : conjugate h (curvature x)=1 ↔ curvature x=1 := by
    simp [conjugate]
  simp only [phaseSign,curvature_gauge,he]
lemma magnetic_covariant (active : Bool) : Covariant (magnetic active) := by
  intro h x y
  have he : gauge h x=gauge h y ↔ x=y := (gaugeEquiv h).injective.eq_iff
  simp [magnetic,Matrix.diagonal_apply,phaseSign_gauge,he]

inductive Gate
  | curvature : Bool → Gate
  | electric : Bool → Gate
  deriving DecidableEq

def gateMatrix : Gate → Matrix Raw Raw ℚ
  | .curvature active => magnetic active
  | .electric e => electric e
lemma gate_transpose (g : Gate) : (gateMatrix g).transpose=gateMatrix g := by
  cases g with
  | curvature b => exact magnetic_transpose b
  | electric e => exact electric_transpose e
lemma gate_square (g : Gate) : gateMatrix g*gateMatrix g=1 := by
  cases g with
  | curvature b => exact magnetic_square b
  | electric e => exact electric_square e
lemma gate_covariant (g : Gate) : Covariant (gateMatrix g) := by
  cases g with
  | curvature b => exact magnetic_covariant b
  | electric e => exact electric_covariant e

def compile : List Gate → Matrix Raw Raw ℚ
  | [] => 1
  | g::w => compile w*gateMatrix g
lemma compile_append (u v : List Gate) : compile (u++v)=compile v*compile u := by
  induction u with
  | nil => simp [compile]
  | cons g u ih => simp only [List.cons_append,compile,ih,mul_assoc]
lemma compile_inverse (w : List Gate) : compile w.reverse=(compile w).transpose := by
  induction w with
  | nil => simp [compile]
  | cons g w ih =>
    simp only [List.reverse_cons,compile_append,compile,Matrix.one_mul,ih,
      Matrix.transpose_mul,gate_transpose]
lemma compile_orthogonal (w : List Gate) : (compile w).transpose*compile w=1 := by
  induction w with
  | nil => simp [compile]
  | cons g w ih =>
    simp only [compile,Matrix.transpose_mul]
    rw [mul_assoc,← mul_assoc (compile w).transpose,ih,one_mul,gate_transpose,gate_square]

lemma covariant_one {R : Type} [CommRing R] : Covariant (1 : Matrix Raw Raw R) := by
  intro h x y
  have he : gauge h x=gauge h y ↔ x=y := (gaugeEquiv h).injective.eq_iff
  simp only [Matrix.one_apply,he]
lemma covariant_mul {R : Type} [CommRing R] (A B : Matrix Raw Raw R)
    (hA : Covariant A) (hB : Covariant B) : Covariant (A*B) := by
  intro h x y
  simp only [Matrix.mul_apply]
  exact Fintype.sum_equiv (gaugeEquiv h).symm _ _ (fun z => by
    let t := (gaugeEquiv h).symm z
    have ht : gauge h t=z := (gaugeEquiv h).apply_symm_apply z
    simpa only [ht] using congrArg₂ (fun a b : R => a*b) (hA h x t) (hB h t y))
lemma compile_covariant (w : List Gate) : Covariant (compile w) := by
  induction w with
  | nil => exact covariant_one
  | cons g w ih => exact covariant_mul _ _ ih (gate_covariant g)
lemma covariant_vacuum {R : Type} [CommRing R] (M : Matrix Raw Raw R)
    (hM : Covariant M) (ψ : Raw → R) (hψ : Vacuum ψ) : Vacuum (M.mulVec ψ) := by
  intro h x
  simp only [Matrix.mulVec,dotProduct]
  exact Fintype.sum_equiv (gaugeEquiv h).symm _ _ (fun z => by
    let t := (gaugeEquiv h).symm z
    have ht : gauge h t=z := (gaugeEquiv h).apply_symm_apply z
    have hp : ψ z=ψ t := by rw [← ht,hψ h t]
    simpa only [ht,hp] using congrArg₂ (fun a b : R => a*b) (hM h x t) (hψ h t))

def tickWord (active : Bool) : List Gate := [.curvature active,.electric false,.electric true]
def tick (active : Bool) : Matrix Raw Raw ℚ := compile (tickWord active)
lemma tick_order (active : Bool) : tick active=electric true*electric false*magnetic active := by
  simp only [tick,tickWord,compile,gateMatrix,Matrix.one_mul]

/-! ## Non-vacuity -/
example : magnetic false=1 := magnetic_off
example : (tick true).transpose*tick true=1 := compile_orthogonal _
end Artform.Scores.Nonabelian
