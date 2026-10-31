import ArtformScores.GravityBridge.LocalityStatements
import ArtformScores.GravityBridge.Stencil

/-! # Processing support, inverse support and channel-scope limits -/

namespace Artform.Scores.GravityBridge

variable {K : Type*} [CommRing K] {d : ℕ}

lemma stencil_radius_add (p q : AddMonoidAlgebra K (Fin d → ℤ)) (r : ℕ)
    (hp : HasStencilRadius p r) (hq : HasStencilRadius q r) : HasStencilRadius (p + q) r := by
  intro a ha i
  have ha' := Finsupp.mem_support_iff.mp ha
  change p.coeff a + q.coeff a ≠ 0 at ha'
  by_cases hp0 : p.coeff a = 0
  · have hq0 : q.coeff a ≠ 0 := by simpa [hp0] using ha'
    exact hq a (Finsupp.mem_support_iff.mpr hq0) i
  · exact hp a (Finsupp.mem_support_iff.mpr hp0) i

lemma stencil_radius_neg (p : AddMonoidAlgebra K (Fin d → ℤ)) (r : ℕ)
    (hp : HasStencilRadius p r) : HasStencilRadius (-p) r := by
  intro a ha i
  have ha' := Finsupp.mem_support_iff.mp ha
  change -p.coeff a ≠ 0 at ha'
  exact hp a (Finsupp.mem_support_iff.mpr (neg_ne_zero.mp ha')) i

lemma matrix_stencil_radius_mul
    (A B : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ)))
    (r s : ℕ) (hA : MatrixStencilRadius A r) (hB : MatrixStencilRadius B s) :
    MatrixStencilRadius (A * B) (r + s) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact stencil_radius_add _ _ _ (stencil_radius_mul _ _ r s (hA i 0) (hB 0 j))
    (stencil_radius_mul _ _ r s (hA i 1) (hB 1 j))

lemma processing_inverse_radius
    (P : Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ)))
    (r : ℕ) (hP : MatrixStencilRadius (P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d →
      ℤ))) r) :
    MatrixStencilRadius (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) r := by
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · exact hP 1 1
  · exact stencil_radius_neg _ _ (hP 0 1)
  · exact stencil_radius_neg _ _ (hP 1 0)
  · exact hP 0 0

lemma processing_conjugate_radius
    (P : Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ)))
    (T : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) (r t : ℕ)
    (hP : MatrixStencilRadius (P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) r) (hT
      : MatrixStencilRadius T t) :
    MatrixStencilRadius ((P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) * T *
      (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))))
      (t + 2 * r) := by
  have h := matrix_stencil_radius_mul _ _ (r + t) r
    (matrix_stencil_radius_mul _ _ r t hP hT) (processing_inverse_radius P r hP)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul] using h

lemma stencil_radius_zero (r : ℕ) : HasStencilRadius (0 : AddMonoidAlgebra K (Fin d → ℤ)) r := by
  simp [HasStencilRadius]

lemma stencil_radius_one (r : ℕ) : HasStencilRadius (1 : AddMonoidAlgebra K (Fin d → ℤ)) r := by
  change HasStencilRadius (AddMonoidAlgebra.single 0 (1 : K)) r
  intro a ha i
  have he : a = 0 := by
    by_contra he
    have hz : (AddMonoidAlgebra.single 0 (1 : K)).coeff a = 0 := by simp [he]
    exact (Finsupp.mem_support_iff.mp ha) hz
  subst a
  simp

lemma matrix_stencil_radius_one :
    MatrixStencilRadius (1 : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact stencil_radius_one 0
  · exact stencil_radius_zero 0
  · exact stencil_radius_zero 0
  · exact stencil_radius_one 0

lemma matrix_stencil_radius_pow
    (T : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) (t n : ℕ)
    (hT : MatrixStencilRadius T t) : MatrixStencilRadius (T ^ n) (n * t) := by
  induction n with
  | zero => simpa using matrix_stencil_radius_one (K := K) (d := d)
  | succ n ih =>
    rw [pow_succ]
    have h := matrix_stencil_radius_mul _ _ (n * t) t ih hT
    simpa [Nat.succ_mul] using h

lemma processing_conjugate_pow
    (P : Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ)))
    (T : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) (n : ℕ) :
    ((P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) * T * ((P⁻¹ :
      Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) :
        Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ)))) ^ n =
      (P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) * T ^ n * ((P⁻¹ :
        Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) :
        Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) := by
  have hp : (P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) * ((P⁻¹ :
    Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) :
        Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hq : ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) :
        Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) * (P : Matrix (Fin 2) (Fin 2)
          (AddMonoidAlgebra K (Fin d → ℤ))) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  induction n with
  | zero => simpa using hp.symm
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc,
      ← Matrix.mul_assoc ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d →
        ℤ))) :
        Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) (P : Matrix (Fin 2) (Fin 2)
          (AddMonoidAlgebra K (Fin d → ℤ))), hq, one_mul]

lemma processing_orbit_radius
    (P : Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ)))
    (T : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) (r t n : ℕ)
    (hP : MatrixStencilRadius (P : Matrix (Fin 2) (Fin 2)
      (AddMonoidAlgebra K (Fin d → ℤ))) r) (hT : MatrixStencilRadius T t) :
    MatrixStencilRadius
      (((P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) * T * ((P⁻¹ :
        Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ))) :
        Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra K (Fin d → ℤ)))) ^ n)
      (n * t + 2 * r) := by
  rw [processing_conjugate_pow]
  exact processing_conjugate_radius P (T ^ n) r (n * t) hP
    (matrix_stencil_radius_pow T t n hT)

lemma three_shear_inverse {S : Type*} [CommRing S] (p : S) :
    threeShear p * threeShearBack p = 1 ∧ threeShearBack p * threeShear p = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [threeShear, threeShearBack, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

lemma three_shear_radius_failure :
    ∃ A Q : Matrix (Fin 3) (Fin 3) (AddMonoidAlgebra ℚ (Fin 1 → ℤ)),
      A * Q = 1 ∧ Q * A = 1 ∧ MatrixStencilRadius A 1 ∧ ¬ MatrixStencilRadius Q 1 := by
  let p : AddMonoidAlgebra ℚ (Fin 1 → ℤ) := AddMonoidAlgebra.single (fun _ => 1) 1
  have hp : HasStencilRadius p 1 := by
    intro a ha i
    have he : a = (fun _ : Fin 1 => (1 : ℤ)) := by simpa [p] using ha
    subst a
    norm_num
  refine ⟨threeShear p, threeShearBack p, (three_shear_inverse p).1,
    (three_shear_inverse p).2, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact stencil_radius_one 1
    · exact hp
    · exact stencil_radius_zero 1
    · exact stencil_radius_zero 1
    · exact stencil_radius_one 1
    · exact hp
    · exact stencil_radius_zero 1
    · exact stencil_radius_zero 1
    · exact stencil_radius_one 1
  · intro h
    have hs : (fun _ : Fin 1 => (2 : ℤ)) ∈ (p ^ 2).coeff.support := by
      dsimp [p]
      simp only [AddMonoidAlgebra.single_pow, nsmul_eq_mul, Nat.cast_ofNat, one_pow,
        AddMonoidAlgebra.coeff_single, ne_eq, one_ne_zero, not_false_eq_true,
        Finsupp.support_single, Finset.mem_singleton]
      ext i
      norm_num
    have hx := h 0 2 _ hs 0
    norm_num at hx

/-- **GAC:local-processing** (account support once at the two processing ends). -/
@[ledger "GAC:local-processing"]
theorem localProcessing : Statement.localProcessing := by
  refine ⟨?_, ?_, three_shear_radius_failure⟩
  · intro K _ d P r hP
    exact processing_inverse_radius P r hP
  · intro K _ d P T r t n hP hT
    exact processing_orbit_radius P T r t n hP hT

/-! ## Non-vacuity -/

example : ∃ P : Matrix.SpecialLinearGroup (Fin 2) (AddMonoidAlgebra ℚ (Fin 1 → ℤ)),
    MatrixStencilRadius (P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra ℚ (Fin 1 → ℤ))) 1 ∧
    MatrixStencilRadius (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra ℚ (Fin 1 → ℤ))) 1 ∧
    ¬ MatrixStencilRadius (P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra ℚ (Fin 1 → ℤ))) 0 := by
  let p : AddMonoidAlgebra ℚ (Fin 1 → ℤ) := AddMonoidAlgebra.single (fun _ => 1) 1
  let P := (Step.move p).sl
  have hp : HasStencilRadius p 1 := by
    intro a ha i
    have he : a = (fun _ : Fin 1 => (1 : ℤ)) := by simpa [p] using ha
    subst a
    norm_num
  have hP : MatrixStencilRadius (P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra ℚ (Fin 1 → ℤ))) 1 :=
    by
    intro i j
    fin_cases i <;> fin_cases j
    · exact stencil_radius_one 1
    · exact hp
    · exact stencil_radius_zero 1
    · exact stencil_radius_one 1
  refine ⟨P, hP, processing_inverse_radius P 1 hP, ?_⟩
  intro h
  have hs : (fun _ : Fin 1 => (1 : ℤ)) ∈ p.coeff.support := by simp [p]
  have hx := h 0 1 _ hs 0
  norm_num at hx

end Artform.Scores.GravityBridge
