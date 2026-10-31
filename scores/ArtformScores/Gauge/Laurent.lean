import Mathlib
/-! # Canonical reversal filters and Weyl separation -/

set_option autoImplicit false
noncomputable section
namespace Artform.Scores.Gauge
open LaurentPolynomial Polynomial
open scoped LaurentPolynomial
variable {R : Type*} [CommRing R]
def symPoly : ℕ → R[X]
  | 0 => 2
  | 1 => X
  | n + 2 => X * symPoly (n + 1) - symPoly n

def waveVar : LaurentPolynomial R := T 1 + T (-1)

lemma symPoly_eval (n : ℕ) :
    Polynomial.eval₂ LaurentPolynomial.C (waveVar : LaurentPolynomial R) (symPoly n) =
      T (n : ℤ) + T (-(n : ℤ)) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [symPoly, LaurentPolynomial.T_zero]
  | one => simp [symPoly, waveVar]
  | more n ih0 ih1 =>
    rw [show symPoly (n + 2) = X * symPoly (n + 1) - symPoly n from rfl,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, ih1, ih0]
    unfold waveVar
    simp only [add_mul, mul_add, ← LaurentPolynomial.T_add]
    have h1 : (1 : ℤ) + (n + 1) = n + 2 := by omega
    have h2 : (1 : ℤ) + -(n + 1) = -n := by omega
    have h3 : (-1 : ℤ) + (n + 1) = n := by omega
    have h4 : (-1 : ℤ) + -(n + 1) = -(n + 2) := by omega
    push_cast
    rw [h1, h2, h3, h4]
    abel

lemma fixed_coeff {f : LaurentPolynomial R} (h : invert f = f) (k : ℤ) :
    f.coeff (-k) = f.coeff k := by
  simpa using congrArg (fun p : LaurentPolynomial R => p.coeff k) h

lemma fixed_decomposition {f : LaurentPolynomial R} (h : invert f = f) :
    f = LaurentPolynomial.C (f.coeff 0) +
      ∑ k ∈ f.coeff.support.filter (fun k : ℤ => 0 < k),
        LaurentPolynomial.C (f.coeff k) * (T k + T (-k)) := by
  ext j
  have hc (k : ℤ) (r : R) :
      (LaurentPolynomial.C r * T k : LaurentPolynomial R).coeff j =
        if k = j then r else 0 := by
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    exact Finsupp.single_apply
  have hc0 (r : R) : (LaurentPolynomial.C r : LaurentPolynomial R).coeff j =
      if 0 = j then r else 0 := by
    simpa only [LaurentPolynomial.T_zero, mul_one] using hc 0 r
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sum,
    Finsupp.add_apply, Finsupp.finsetSum_apply, mul_add]
  simp_rw [hc, hc0]
  have hs : ∀ k : ℤ, (-k = j) ↔ k = -j := by intro k; omega
  have h0 : (0 : ℤ) = j ↔ j = 0 := eq_comm
  simp only [hs, h0, Finset.sum_add_distrib, Finset.sum_ite_eq']
  by_cases hj0 : j = 0
  · subst j
    simp
  · by_cases hj : 0 < j
    · have hn : ¬ 0 < -j := by omega
      simp only [hj0, ite_false, zero_add, Finset.mem_filter, hj, hn, and_true,
        and_false, ite_false, add_zero]
      by_cases hm : j ∈ f.coeff.support
      · simp [hm]
      · simp [hm, Finsupp.notMem_support_iff.mp hm]
    · have hp : 0 < -j := by omega
      simp only [hj0, ite_false, zero_add, Finset.mem_filter, hj, hp, and_true,
        and_false, ite_false]
      by_cases hm : -j ∈ f.coeff.support
      · simp [hm, fixed_coeff h j]
      · have hz := Finsupp.notMem_support_iff.mp hm
        rw [fixed_coeff h j] at hz
        simp [hm, hz]

lemma fixed_iff_polynomial (f : LaurentPolynomial R) :
    invert f = f ↔ ∃ p : R[X], Polynomial.eval₂ LaurentPolynomial.C waveVar p = f := by
  constructor
  · intro h
    refine ⟨Polynomial.C (f.coeff 0) +
      ∑ k ∈ f.coeff.support.filter (fun k : ℤ => 0 < k),
        Polynomial.C (f.coeff k) * symPoly k.toNat, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_finsetSum]
    simp_rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, symPoly_eval]
    conv_rhs => rw [fixed_decomposition h]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Int.toNat_of_nonneg (le_of_lt (Finset.mem_filter.mp hk).2)]
  · rintro ⟨p, rfl⟩
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.eval₂_add, map_add, hp, hq]
    | monomial n a =>
      simp [Polynomial.eval₂_monomial, waveVar, map_add, add_comm]

def canonical (a b c d : LaurentPolynomial R) : Prop :=
  invert a * c - invert c * a = 0 ∧ invert a * d - invert c * b = 1 ∧
  invert b * c - invert d * a = -1 ∧ invert b * d - invert d * b = 0

lemma det_filter {S : Type*} [CommRing S]
    (a b c d A B C D : S) (hdet : a * d - b * c = 1) :
    (A*c-C*a=0 ∧ A*d-C*b=1 ∧ B*c-D*a = -1 ∧ B*d-D*b=0) ↔
      (A=a ∧ B=b ∧ C=c ∧ D=d) := by
  constructor
  · rintro ⟨h11,h12,h21,h22⟩
    refine ⟨?_,?_,?_,?_⟩
    · linear_combination -A*hdet+a*h12-b*h11
    · linear_combination -B*hdet+a*h22-b*h21
    · linear_combination -C*hdet+c*h12-d*h11
    · linear_combination -D*hdet+c*h22-d*h21
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    refine ⟨by ring,?_,?_,by ring⟩
    · linear_combination hdet
    · linear_combination -hdet

lemma canonical_iff (a b c d : LaurentPolynomial R) (hdet : a * d - b * c = 1) :
    canonical a b c d ↔ invert a=a ∧ invert b=b ∧ invert c=c ∧ invert d=d :=
  det_filter a b c d (invert a) (invert b) (invert c) (invert d) hdet

lemma canonical_matrix (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial R)) :
    (P.transpose.map invert) * !![0,1;-1,0] * P = !![0,1;-1,0] ↔
      canonical (P 0 0) (P 0 1) (P 1 0) (P 1 1) := by
  constructor
  · intro h
    have h00 := congrArg (fun M => M 0 0) h
    have h01 := congrArg (fun M => M 0 1) h
    have h10 := congrArg (fun M => M 1 0) h
    have h11 := congrArg (fun M => M 1 1) h
    simp only [Fin.isValue, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_neg, mul_one, zero_add,
      neg_mul, add_zero] at h00 h01 h10 h11
    exact ⟨by linear_combination h00, by linear_combination h01,
      by linear_combination h10, by linear_combination h11⟩
  · rintro ⟨h00,h01,h10,h11⟩
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.transpose_apply]
    · linear_combination h00
    · linear_combination h01
    · linear_combination h10
    · linear_combination h11

def laplacianVar : LaurentPolynomial R := 2-waveVar
lemma fixed_iff_laplacian (f : LaurentPolynomial R) :
    invert f=f ↔ ∃ p : R[X], Polynomial.eval₂ LaurentPolynomial.C laplacianVar p=f := by
  rw [fixed_iff_polynomial]
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨p.comp (Polynomial.C 2-X), ?_⟩
    rw [Polynomial.eval₂_comp]
    norm_num only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, map_ofNat]
    convert hp using 1
    congr 1
    unfold laplacianVar
    ring
  · rintro ⟨p,hp⟩
    refine ⟨p.comp (Polynomial.C 2-X), ?_⟩
    rw [Polynomial.eval₂_comp]
    norm_num only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, map_ofNat]
    exact hp

lemma matrix_filter (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial R)) (h : P.det = 1) :
    ((P.transpose.map invert) * !![0,1;-1,0] * P = !![0,1;-1,0]) ↔
      ∀ i j, invert (P i j)=P i j := by
  rw [canonical_matrix, canonical_iff _ _ _ _ (by simpa [Matrix.det_fin_two] using h)]
  constructor
  · rintro ⟨ha,hb,hc,hd⟩ i j
    fin_cases i <;> fin_cases j <;> assumption
  · intro hP
    exact ⟨hP 0 0,hP 0 1,hP 1 0,hP 1 1⟩

abbrev Phase5 := (Fin 5 → ZMod 3) × (Fin 5 → ZMod 3)
def lap5 (a : Fin 5 → ZMod 3) (i : Fin 5) : ZMod 3 :=
  2*a i-a (i+1)-a (i+4)
def tick5 (s : Phase5) : Phase5 :=
  let ep := fun i => s.2 i+lap5 s.1 i
  (fun i => s.1 i-ep i,ep)
def processor5 (s : Phase5) : Phase5 := (fun i => s.1 (i+1),fun i => s.2 (i+4))
def inverse5 (s : Phase5) : Phase5 := (fun i => s.1 (i+4),fun i => s.2 (i+1))
def processed5 (s : Phase5) : Phase5 := processor5 (tick5 (inverse5 s))
def pairing5 (u v : Phase5) : ZMod 3 := ∑ i, (u.1 i*v.2 i-u.2 i*v.1 i)
def a0 : Phase5 := (fun i => if i.val=0 then 1 else 0,0)
def a1 : Phase5 := (fun i => if i.val=1 then 1 else 0,0)
def common5 (s : Phase5) : Phase5 := (fun i => s.1 (i+1),fun i => s.2 (i+1))
lemma common_canonical (u v : Phase5) : pairing5 (common5 u) (common5 v)=pairing5 u v := by
  simp [pairing5,common5,Fin.sum_univ_succ]
  ring
lemma processed_obstruction : pairing5 a0 a1=0 ∧ pairing5 (processed5 a0) (processed5 a1)=2 := by
  decide +kernel
lemma weyl_obstruction :
    ZMod.stdAddChar (pairing5 a0 a1) = (1:ℂ) ∧
    ZMod.stdAddChar (pairing5 (processed5 a0) (processed5 a1)) ≠ (1:ℂ) := by
  constructor
  · rw [processed_obstruction.1,AddChar.map_zero_eq_one]
  · intro h
    have he := ZMod.injective_stdAddChar
      (h.trans (AddChar.map_zero_eq_one ZMod.stdAddChar).symm)
    rw [processed_obstruction.2] at he
    exact (by decide : (2:ZMod 3) ≠ 0) he

def weyl5 (u : Phase5) (ψ : (Fin 5 → ZMod 3) → ℂ) (x : Fin 5 → ZMod 3) : ℂ :=
  ZMod.stdAddChar (∑ i, u.2 i*x i) * ψ (x+u.1)
lemma weyl_commutator (u v : Phase5) (ψ : (Fin 5 → ZMod 3) → ℂ) (x : Fin 5 → ZMod 3) :
    weyl5 u (weyl5 v ψ) x =
      ZMod.stdAddChar (pairing5 u v) * weyl5 v (weyl5 u ψ) x := by
  have hp : x+u.1+v.1=x+v.1+u.1 := by abel
  simp only [weyl5, hp]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [pairing5, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add]
  simp_rw [mul_comm]
  ring

abbrev Wave5 := (Fin 5 → ZMod 3) → ℂ
noncomputable def weylOp (u : Phase5) : Wave5 →ₗ[ℂ] Wave5 where
  toFun := weyl5 u
  map_add' ψ η := by funext x; simp [weyl5,mul_add]
  map_smul' r ψ := by funext x; simp [weyl5,mul_left_comm]
lemma old_commutes : weylOp a0 * weylOp a1 = weylOp a1 * weylOp a0 := by
  apply LinearMap.ext
  intro ψ
  funext x
  change weyl5 a0 (weyl5 a1 ψ) x = weyl5 a1 (weyl5 a0 ψ) x
  have hc := weyl_commutator a0 a1 ψ x
  simpa only [processed_obstruction.1,AddChar.map_zero_eq_one,one_mul] using hc
lemma new_not_commutes :
    weylOp (processed5 a0) * weylOp (processed5 a1) ≠
      weylOp (processed5 a1) * weylOp (processed5 a0) := by
  intro h
  have hz (t : ZMod 3) : ZMod.stdAddChar t ≠ (0:ℂ) := by
    intro he
    have ht := AddChar.map_add_eq_mul ZMod.stdAddChar t (-t)
    simp [he] at ht
  let ψ : Wave5 := fun _ => 1
  let x : Fin 5 → ZMod 3 := 0
  have hr : weyl5 (processed5 a1) (weyl5 (processed5 a0) ψ) x ≠ 0 := by
    simp only [weyl5,ψ,mul_one]
    exact mul_ne_zero (hz _) (hz _)
  have hc := weyl_commutator (processed5 a0) (processed5 a1) ψ x
  have he := congrArg (fun M : Wave5 →ₗ[ℂ] Wave5 => M ψ x) h
  change weyl5 (processed5 a0) (weyl5 (processed5 a1) ψ) x =
    weyl5 (processed5 a1) (weyl5 (processed5 a0) ψ) x at he
  rw [he] at hc
  have hc' : ZMod.stdAddChar (pairing5 (processed5 a0) (processed5 a1))=1 := by
    apply (mul_right_cancel₀ hr)
    exact hc.symm.trans (one_mul _).symm
  exact weyl_obstruction.2 hc'

lemma no_processed_conjugacy :
    ¬ ∃ U : Wave5 ≃ₗ[ℂ] Wave5, ∀ u : Phase5,
      (U : Wave5 →ₗ[ℂ] Wave5) * weylOp u * (U.symm : Wave5 →ₗ[ℂ] Wave5) =
        weylOp (processed5 u) := by
  rintro ⟨U,hU⟩
  apply new_not_commutes
  rw [← hU a0,← hU a1]
  have hInv : (U.symm : Wave5 →ₗ[ℂ] Wave5) * (U : Wave5 →ₗ[ℂ] Wave5)=1 := by
    apply LinearMap.ext; intro ψ; exact U.symm_apply_apply ψ
  calc
    _ = (U : Wave5 →ₗ[ℂ] Wave5) * (weylOp a0 * weylOp a1) *
        (U.symm : Wave5 →ₗ[ℂ] Wave5) := by
          simp only [mul_assoc,← mul_assoc (U.symm : Wave5 →ₗ[ℂ] Wave5),hInv,one_mul]
    _ = (U : Wave5 →ₗ[ℂ] Wave5) * (weylOp a1 * weylOp a0) *
        (U.symm : Wave5 →ₗ[ℂ] Wave5) := by rw [old_commutes]
    _ = _ := by
      simp only [mul_assoc,← mul_assoc (U.symm : Wave5 →ₗ[ℂ] Wave5),hInv,one_mul]

end Artform.Scores.Gauge
