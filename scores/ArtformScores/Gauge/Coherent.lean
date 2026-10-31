import ArtformScores.Gauge.Process
/-! # Calibrated C8 receipts and phase-aware vacuum compilation -/

set_option autoImplicit false
noncomputable section
namespace Artform.Scores.Gauge
open Finset
abbrev C8 := ZMod 8
abbrev C16 := ZMod 16

def lift8 (x : C8) : C16 := (x.val : C16)
def doubled (x : C8) : C16 := 2 * lift8 x
lemma doubled_add : ∀ x y : C8, doubled (x+y) = doubled x+doubled y := by decide +kernel
lemma doubled_injective : Function.Injective doubled := by decide +kernel

def χ : AddChar C8 ℂ where
  toFun x := ZMod.stdAddChar (doubled x)
  map_zero_eq_one' := by simp [doubled, lift8]
  map_add_eq_mul' x y := by rw [doubled_add, AddChar.map_add_eq_mul]

lemma χ_injective : Function.Injective χ := by
  intro x y h
  exact doubled_injective (ZMod.injective_stdAddChar h)
lemma χ_primitive : χ.IsPrimitive := by
  apply AddChar.zmod_char_primitive_of_eq_one_only_at_zero
  intro t ht
  exact χ_injective (by simpa only [AddChar.map_zero_eq_one] using ht)
lemma χ_sum (t : C8) : ∑ e : C8, χ (t*e) = if t=0 then 8 else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (χ_primitive h)

lemma char_star (x : C16) : star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle x)).symm.trans
    (congrArg (fun z : Circle => (z : ℂ)) (AddChar.map_neg_eq_inv ZMod.toCircle x).symm)
lemma doubled_neg : ∀ x : C8, doubled (-x) = -doubled x := by decide +kernel
lemma χ_star (x : C8) : star (χ x) = χ (-x) := by
  change star (ZMod.stdAddChar (doubled x)) = ZMod.stdAddChar (doubled (-x))
  rw [char_star, doubled_neg]

def qExponent (negative : Bool) (x : C8) : C16 :=
  -(lift8 x)^2 + if negative then 8*lift8 x else 0
def q (negative : Bool) (x : C8) : ℂ := ZMod.stdAddChar (qExponent negative x)
lemma q_receipt_exponent : ∀ b : Bool, ∀ s t : C8,
    qExponent b (s+t) = qExponent b s+qExponent b t - doubled (s*t) := by decide +kernel
lemma q_even_exponent : ∀ b : Bool, ∀ x : C8, qExponent b (-x) = qExponent b x := by decide +kernel
lemma q_receipt (b : Bool) (s t : C8) :
    q b (s+t) = q b s*q b t*χ (-(s*t)) := by
  change ZMod.stdAddChar _ = _ * _ * ZMod.stdAddChar (doubled (-(s*t)))
  rw [q_receipt_exponent]
  rw [doubled_neg]
  simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, q]
lemma q_even (b : Bool) (x : C8) : q b (-x) = q b x :=
  congrArg (ZMod.stdAddChar : C16 → ℂ) (q_even_exponent b x)
lemma q_zero (b : Bool) : q b 0 = 1 := by cases b <;> simp [q,qExponent,lift8]
lemma q_unit (b : Bool) (x : C8) : star (q b x)*q b x = 1 := by
  rw [q, char_star, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

/-- MQ7, as an amplitude matrix: input y, output x, increment x-y. -/
def kineticKernel (b : Bool) (a : C8) : ℂ :=
  (8:ℂ)⁻¹ * ∑ e : C8, q b e * χ (-(e*a))
def kinetic (b : Bool) : Matrix C8 C8 ℂ := fun x y => kineticKernel b (x-y)

def fourier : Matrix C8 C8 ℂ := fun e x => χ (e*x)
lemma fourier_orthogonal : fourier.conjTranspose * fourier = (8:ℂ) • (1 : Matrix C8 C8 ℂ) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fourier, χ_star,
    ← AddChar.map_add_eq_mul]
  simp_rw [show ∀ e : C8, -(e*x)+e*y = (y-x)*e by intro e; ring]
  rw [χ_sum]
  by_cases h : x=y
  · subst y; simp
  · simp [h, sub_ne_zero.mpr (Ne.symm h)]
lemma fourier_orthogonal' : fourier * fourier.conjTranspose = (8:ℂ) • (1 : Matrix C8 C8 ℂ) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fourier, χ_star,
    ← AddChar.map_add_eq_mul]
  simp_rw [show ∀ e : C8, x*e + -(y*e) = (x-y)*e by intro e; ring]
  rw [χ_sum]
  by_cases h : x=y
  · subst y; simp
  · simp [h, sub_ne_zero.mpr h]

def diagonalQ (b : Bool) : Matrix C8 C8 ℂ := Matrix.diagonal (q b)
lemma diagonalQ_unit (b : Bool) : (diagonalQ b).conjTranspose * diagonalQ b = 1 := by
  simp only [diagonalQ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  change Matrix.diagonal (fun i => star (q b i) * q b i) = 1
  simp only [q_unit, Matrix.diagonal_one]

lemma kinetic_factor (b : Bool) : kinetic b =
    (8:ℂ)⁻¹ • (fourier.conjTranspose * (diagonalQ b * fourier)) := by
  apply Matrix.ext
  intro x y
  simp only [diagonalQ, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    fourier, χ_star, kinetic, kineticKernel, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]
  rw [show -(e*(x-y)) = -(e*x)+e*y by ring, AddChar.map_add_eq_mul]
  ring

lemma kinetic_unitary (b : Bool) : (kinetic b).conjTranspose * kinetic b = 1 := by
  have hA :
      (fourier.conjTranspose * ((diagonalQ b).conjTranspose * fourier)) *
      (fourier.conjTranspose * (diagonalQ b * fourier)) = (64:ℂ) • (1 : Matrix C8 C8 ℂ) := by
    calc
      _ = fourier.conjTranspose * ((diagonalQ b).conjTranspose *
          ((fourier * fourier.conjTranspose) * (diagonalQ b * fourier))) := by
            simp only [Matrix.mul_assoc]
      _ = (8:ℂ) • (fourier.conjTranspose *
          (((diagonalQ b).conjTranspose * diagonalQ b) * fourier)) := by
            rw [fourier_orthogonal']
            simp [Matrix.mul_assoc]
      _ = (64:ℂ) • (1 : Matrix C8 C8 ℂ) := by
        rw [diagonalQ_unit]
        norm_num [fourier_orthogonal, smul_smul]
  rw [kinetic_factor]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show fourier.conjTranspose * (diagonalQ b).conjTranspose * fourier =
    fourier.conjTranspose * ((diagonalQ b).conjTranspose * fourier) by rw [Matrix.mul_assoc], hA]
  norm_num [smul_smul]

lemma kinetic_unitary_other (b : Bool) : kinetic b * (kinetic b).conjTranspose = 1 :=
  mul_eq_one_comm.mp (kinetic_unitary b)

variable (K : Artform.Canvas)
abbrev Config := K.E → C8

def edgeMatrix (e : K.E) (b : Bool) : Matrix (Config K) (Config K) ℂ :=
  (Matrix.kroneckerMap (· * ·) (kinetic b) (1 : Matrix ({f : K.E // f ≠ e} → C8)
    ({f : K.E // f ≠ e} → C8) ℂ)).submatrix
      (Equiv.funSplitAt e C8) (Equiv.funSplitAt e C8)

lemma edge_unitary (e : K.E) (b : Bool) :
    (edgeMatrix K e b).conjTranspose * edgeMatrix K e b = 1 := by
  unfold edgeMatrix
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    kinetic_unitary, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

def faceMatrix (p : K.F) (b : Bool) : Matrix (Config K) (Config K) ℂ :=
  Matrix.diagonal (fun x => q b (K.curl x p))
lemma face_unitary (p : K.F) (b : Bool) :
    (faceMatrix K p b).conjTranspose * faceMatrix K p b = 1 := by
  simp only [faceMatrix, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  change Matrix.diagonal (fun x => star (q b (K.curl x p))*q b (K.curl x p)) = 1
  simp only [q_unit, Matrix.diagonal_one]

/-- Invariance under simultaneous translation of both matrix indices. -/
def Covariant (h : Config K) (M : Matrix (Config K) (Config K) ℂ) : Prop :=
  ∀ x y, M (x+h) (y+h) = M x y

lemma edge_covariant (e : K.E) (b : Bool) (h : Config K) : Covariant K h (edgeMatrix K e b) := by
  classical
  intro x y
  have hr : (fun f : {f : K.E // f ≠ e} => (x+h) f) = (fun f : {f : K.E // f ≠ e} => (y+h) f) ↔
      (fun f : {f : K.E // f ≠ e} => x f) = (fun f : {f : K.E // f ≠ e} => y f) := by
    constructor
    · intro he; funext f; exact add_right_cancel (congrFun he f)
    · intro he; funext f; exact congrArg (fun z => z+h f) (congrFun he f)
  simp only [edgeMatrix, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.funSplitAt_apply, kinetic, Matrix.one_apply]
  simp only [Pi.add_apply, add_sub_add_right_eq_sub]
  simp only [Pi.add_apply] at hr
  simp only [hr]

lemma face_covariant (p : K.F) (b : Bool) (φ : K.V → C8) :
    Covariant K (K.diff φ) (faceMatrix K p b) := by
  intro x y
  have he : x+K.diff φ = y+K.diff φ ↔ x=y := add_left_inj _
  simp [faceMatrix, Matrix.diagonal_apply, he]

lemma covariant_one (h : Config K) : Covariant K h 1 := by
  intro x y
  simp [Matrix.one_apply]
lemma covariant_mul (h : Config K) (A B : Matrix (Config K) (Config K) ℂ)
    (ha : Covariant K h A) (hb : Covariant K h B) : Covariant K h (A*B) := by
  intro x y
  simp only [Matrix.mul_apply]
  exact Fintype.sum_equiv (Equiv.addRight h).symm _ _ (fun z => by
    simp only [Equiv.addRight_symm_apply]
    change A (x+h) z * B z (y+h) = A x (z + -h) * B (z + -h) y
    rw [← ha x (z + -h), ← hb (z + -h) y]
    simp)

lemma covariant_star (h : Config K) (A : Matrix (Config K) (Config K) ℂ)
    (ha : Covariant K h A) : Covariant K h A.conjTranspose := by
  intro x y
  exact congrArg star (ha y x)

inductive CoherentGate
  | face : K.F → Bool → CoherentGate
  | move : K.E → Bool → CoherentGate

def gateMatrix (g : CoherentGate K) : Matrix (Config K) (Config K) ℂ := match g with
  | .face p b => faceMatrix K p b
  | .move e b => edgeMatrix K e b

def letterMatrix (l : CoherentGate K × Bool) : Matrix (Config K) (Config K) ℂ :=
  if l.2 then (gateMatrix K l.1).conjTranspose else gateMatrix K l.1

def compile : List (CoherentGate K × Bool) → Matrix (Config K) (Config K) ℂ
  | [] => 1
  | g::w => compile w * letterMatrix K g

lemma letter_unitary (l : CoherentGate K × Bool) :
    (letterMatrix K l).conjTranspose * letterMatrix K l = 1 := by
  have hg : (gateMatrix K l.1).conjTranspose * gateMatrix K l.1 = 1 := by
    cases l.1 with
    | face p b => exact face_unitary K p b
    | move e b => exact edge_unitary K e b
  unfold letterMatrix
  split_ifs
  · simpa only [Matrix.conjTranspose_conjTranspose] using mul_eq_one_comm.mp hg
  · exact hg
lemma compile_unitary (w : List (CoherentGate K × Bool)) :
    (compile K w).conjTranspose * compile K w = 1 := by
  induction w with
  | nil => simp [compile]
  | cons g w ih =>
    simp only [compile, Matrix.conjTranspose_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (compile K w).conjTranspose,
      ih, Matrix.one_mul, letter_unitary]

lemma compile_covariant (w : List (CoherentGate K × Bool)) (φ : K.V → C8) :
    Covariant K (K.diff φ) (compile K w) := by
  induction w with
  | nil => exact covariant_one K _
  | cons l w ih =>
    apply covariant_mul K _ _ _ ih
    have hg : Covariant K (K.diff φ) (gateMatrix K l.1) := by
      cases l.1 with
      | face p b => exact face_covariant K p b φ
      | move e b => exact edge_covariant K e b _
    unfold letterMatrix
    split_ifs
    · exact covariant_star K _ _ hg
    · exact hg

def Vacuum (ψ : Config K → ℂ) : Prop := ∀ φ x, ψ (x+K.diff φ) = ψ x
lemma compile_vacuum (w : List (CoherentGate K × Bool)) (ψ : Config K → ℂ)
    (hψ : Vacuum K ψ) : Vacuum K ((compile K w).mulVec ψ) := by
  intro φ x
  let h := K.diff φ
  simp only [Matrix.mulVec, dotProduct]
  exact Fintype.sum_equiv (Equiv.addRight h).symm _ _ (fun z => by
    simp only [Equiv.addRight_symm_apply]
    change compile K w (x+h) z * ψ z = compile K w x (z + -h) * ψ (z + -h)
    rw [← compile_covariant K w φ x (z + -h), ← hψ φ (z + -h)]
    simp [h])

lemma compile_append (u v : List (CoherentGate K × Bool)) :
    compile K (u++v) = compile K v * compile K u := by
  induction u with
  | nil => simp [compile]
  | cons g u ih => simp only [List.cons_append, compile, ih, Matrix.mul_assoc]

def invertLetter (l : CoherentGate K × Bool) : CoherentGate K × Bool := (l.1, !l.2)
lemma letter_inverse (l : CoherentGate K × Bool) :
    letterMatrix K (invertLetter K l) = (letterMatrix K l).conjTranspose := by
  rcases l with ⟨g,b⟩
  cases b <;> simp [invertLetter, letterMatrix]
lemma compile_inverse (w : List (CoherentGate K × Bool)) :
    compile K (w.reverse.map (invertLetter K)) = (compile K w).conjTranspose := by
  induction w with
  | nil => simp [compile]
  | cons g w ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      compile_append, compile, Matrix.one_mul, ih, letter_inverse, Matrix.conjTranspose_mul]

/-- The actual coefficient extension, embedded in ℂ. No palette enlargement. -/
def receiptRing : Subring ℂ := Subring.closure {ZMod.stdAddChar (1:C16), (2:ℂ)⁻¹}
lemma char_mem (x : C16) : ZMod.stdAddChar x ∈ receiptRing := by
  have hx : ZMod.stdAddChar x = ZMod.stdAddChar (1:C16) ^ x.val := by
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    simp [nsmul_eq_mul]
  rw [hx]
  exact receiptRing.pow_mem (Subring.subset_closure (by simp)) _
lemma eighth_mem : (8:ℂ)⁻¹ ∈ receiptRing := by
  have h : (8:ℂ)⁻¹ = ((2:ℂ)⁻¹)^3 := by norm_num
  rw [h]
  exact receiptRing.pow_mem (Subring.subset_closure (by simp)) _
lemma q_mem (b : Bool) (x : C8) : q b x ∈ receiptRing := char_mem _
lemma kernel_mem (b : Bool) (a : C8) : kineticKernel b a ∈ receiptRing := by
  apply receiptRing.mul_mem eighth_mem
  apply receiptRing.sum_mem
  intro e _
  exact receiptRing.mul_mem (q_mem b e) (char_mem _)

lemma receipts_distinct : q false 1 ≠ q true 1 := by
  intro h
  have he := ZMod.injective_stdAddChar h
  exact (by decide : qExponent false 1 ≠ qExponent true 1) he
lemma receipt_eighth (b : Bool) : (q b 1)^8 ≠ 1 := by
  intro h
  have hz : (8:ℕ) • qExponent b 1 ≠ 0 := by cases b <;> decide +kernel
  have he : ZMod.stdAddChar ((8:ℕ) • qExponent b 1) = ZMod.stdAddChar (0:C16) := by
    rw [AddChar.map_nsmul_eq_pow, AddChar.map_zero_eq_one]
    exact h
  exact hz (ZMod.injective_stdAddChar he)
lemma inverse_kernel (b : Bool) (x y : C8) :
    (kinetic b).conjTranspose x y = star (kineticKernel b (-(x-y))) := by
  simp only [Matrix.conjTranspose_apply, kinetic]
  congr 2
  ring

lemma edge_actual (e : K.E) (b : Bool) (x y : Config K) :
    edgeMatrix K e b x y = kineticKernel b (x e-y e) *
      if (fun f : {f : K.E // f ≠ e} => x f) = (fun f : {f : K.E // f ≠ e} => y f)
      then 1 else 0 := by
  rfl

lemma kernel_star_mem (b : Bool) (a : C8) : star (kineticKernel b a) ∈ receiptRing := by
  unfold kineticKernel
  simp only [star_mul, star_sum, χ_star]
  have h8 : star ((8:ℂ)⁻¹)=(8:ℂ)⁻¹ := by norm_num
  rw [h8]
  apply receiptRing.mul_mem
  · apply receiptRing.sum_mem
    intro e _
    exact receiptRing.mul_mem (char_mem _)
      (by simpa only [q,char_star] using char_mem (-qExponent b e))
  · exact eighth_mem

lemma gate_mem (g : CoherentGate K) (x y : Config K) :
    gateMatrix K g x y ∈ receiptRing ∧ star (gateMatrix K g x y) ∈ receiptRing := by
  cases g with
  | face p b =>
    simp only [gateMatrix,faceMatrix,Matrix.diagonal_apply]
    split_ifs
    · exact ⟨q_mem b _, by simpa only [q,char_star] using char_mem (-qExponent b (K.curl x p))⟩
    · simp
  | move e b =>
    simp only [gateMatrix,edge_actual]
    split_ifs
    · simpa only [mul_one] using And.intro (kernel_mem b (x e-y e)) (kernel_star_mem b (x e-y e))
    · simp

lemma compile_mem (w : List (CoherentGate K × Bool)) (x y : Config K) :
    compile K w x y ∈ receiptRing := by
  induction w generalizing x y with
  | nil => simp [compile,Matrix.one_apply]; split_ifs <;> simp
  | cons g w ih =>
    simp only [compile,Matrix.mul_apply]
    apply receiptRing.sum_mem
    intro z _
    apply receiptRing.mul_mem (ih x z)
    unfold letterMatrix
    split_ifs
    · exact (gate_mem K g.1 y z).2
    · exact (gate_mem K g.1 z y).1

lemma χ_standard (x : C8) : χ x = ZMod.stdAddChar x := by
  change ZMod.stdAddChar (2*(x.val:C16))=ZMod.stdAddChar x
  rw [show (2*(x.val:C16))=((2*(x.val:ℤ):ℤ):C16) by push_cast; rfl]
  rw [ZMod.stdAddChar_coe]
  conv_rhs => rw [← ZMod.natCast_zmod_val x]
  rw [show (x.val:C8)=((x.val:ℤ):C8) by simp]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- The native MQ9 library uses one common q policy and keeps kick before move. -/
def vacuumWord (b : Bool) : List (CoherentGate K × Bool) :=
  (Finset.univ.toList.map (fun p => (.face p b,false))) ++
  (Finset.univ.toList.map (fun e => (.move e b,false)))
lemma compile_face_list (b : Bool) (ps : List K.F) :
    compile K (ps.map (fun p => (.face p b,false))) =
      Matrix.diagonal (fun x => (ps.map (fun p => q b (K.curl x p))).prod) := by
  induction ps with
  | nil => simp [compile]
  | cons p ps ih =>
    simp only [List.map_cons,compile,letterMatrix,Bool.false_eq_true,ite_false,
      gateMatrix,faceMatrix,ih,Matrix.diagonal_mul_diagonal,List.prod_cons]
    congr 1
    funext x
    exact mul_comm _ _
lemma compile_gate_list (gs : List (CoherentGate K)) :
    compile K (gs.map (fun g => (g,false)))=(gs.reverse.map (gateMatrix K)).prod := by
  induction gs with
  | nil => simp [compile]
  | cons g gs ih =>
    simp only [List.map_cons,compile,letterMatrix,Bool.false_eq_true,ite_false,ih,
      List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.prod_append,
      List.prod_cons,List.prod_nil,mul_one]
lemma vacuum_factor (b : Bool) :
    compile K (vacuumWord K b)=
      ((Finset.univ.toList.reverse.map (fun e => edgeMatrix K e b)).prod) *
      Matrix.diagonal (fun x => ∏ p, q b (K.curl x p)) := by
  rw [vacuumWord,compile_append,compile_face_list]
  have hm := compile_gate_list K (Finset.univ.toList.map (fun e => CoherentGate.move e b))
  simp only [List.map_map,Function.comp_def,List.map_reverse,gateMatrix] at hm
  rw [hm]
  simp only [Finset.prod_map_toList,List.map_reverse]

abbrev configurationFrame : Artform.Presentation := ⟨K.E,fun _ => C8⟩
def translationProfile (e : K.E) (a : C8) : Artform.ProcessProfile (configurationFrame K) where
  guard _ := True
  reads := {e}
  writes := {e}
  update x := Function.update x e (x e+a)
  guard_reads _ _ _ := Iff.rfl
  update_reads x y h f hf := by
    have hf' : f=e := hf
    subst f
    simp only [Function.update_self]
    rw [h e (Set.mem_singleton e)]
lemma translation_apply (e : K.E) (a : C8) (x : Config K) :
    (translationProfile K e a).apply x=Function.update x e (x e+a) := by
  classical
  funext f
  by_cases hf : f=e
  · subst f
    simp [Artform.ProcessProfile.apply,translationProfile]
  · simp [Artform.ProcessProfile.apply,translationProfile,hf]
lemma edge_translation (e : K.E) (b : Bool) (a : C8) (x : Config K) :
    edgeMatrix K e b ((translationProfile K e a).apply x) x=kineticKernel b a := by
  rw [translation_apply,edge_actual]
  have hr : (fun f : {f : K.E // f ≠ e} => Function.update x e (x e+a) f)=
      (fun f : {f : K.E // f ≠ e} => x f) := by
    funext f
    exact Function.update_of_ne f.property _ _
  simp [hr]

end Artform.Scores.Gauge
