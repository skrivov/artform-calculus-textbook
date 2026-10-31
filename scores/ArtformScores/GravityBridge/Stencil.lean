import ArtformScores.GravityBridge.StencilStatements
import ArtformScores.Rules

/-! # Stencil composition, support, sharp radius bounds and restricted readings -/

namespace Artform.Scores.GravityBridge

open scoped Pointwise

variable {K G : Type*} [Semiring K] [AddMonoid G]

lemma stencilAct_single (a : G) (c : K) (v : G → K) (x : G) :
    stencilAct (AddMonoidAlgebra.single a c) v x = c * v (x + a) := by
  simp [stencilAct]

lemma stencilAct_add (p q : AddMonoidAlgebra K G) (v : G → K) (x : G) :
    stencilAct (p + q) v x = stencilAct p v x + stencilAct q v x := by
  classical
  simp [stencilAct, Finsupp.sum_add_index, add_mul]

lemma stencilAct_zero (v : G → K) (x : G) : stencilAct (0 : AddMonoidAlgebra K G) v x = 0 := by
  simp [stencilAct]

lemma stencilAct_mul (p q : AddMonoidAlgebra K G) (v : G → K) (x : G) :
    stencilAct (p * q) v x = stencilAct p (fun y => stencilAct q v y) x := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp [stencilAct_zero]
  | add p1 p2 h1 h2 => rw [add_mul, stencilAct_add, stencilAct_add, h1, h2]
  | single a c =>
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp [stencilAct_zero, stencilAct_single]
    | add q1 q2 h1 h2 =>
      rw [mul_add, stencilAct_add, h1, h2]
      simp [stencilAct_single, stencilAct_add, mul_add]
    | single b d =>
      simp [AddMonoidAlgebra.single_mul_single, stencilAct_single, mul_assoc, add_assoc]

lemma stencil_support_mul [DecidableEq G] (p q : AddMonoidAlgebra K G) :
    (p * q).coeff.support ⊆ p.coeff.support + q.coeff.support :=
  AddMonoidAlgebra.support_coeff_mul_subset p q

lemma stencil_radius_mul {d : ℕ} (p q : AddMonoidAlgebra K (Fin d → ℤ))
    (r s : ℕ) (hp : HasStencilRadius p r) (hq : HasStencilRadius q s) :
    HasStencilRadius (p * q) (r + s) := by
  intro a ha i
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.mem_add.mp (stencil_support_mul p q ha)
  rw [← hbc]
  exact (Int.natAbs_add_le (b i) (c i)).trans (Nat.add_le_add (hp b hb i) (hq c hc i))

lemma averaging_constant (n : ℕ) (c : ℚ) :
    Matrix.mulVec (averagingMatrix n) (fun _ => c) = fun _ => c := by
  have hn : (n + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  funext i
  simp [averagingMatrix, Matrix.mulVec, dotProduct, nsmul_eq_mul]
  field_simp

lemma averaging_dense (n : ℕ) (i j : Fin (n + 1)) : averagingMatrix n i j ≠ 0 := by
  have hn : (n + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact div_ne_zero (by norm_num) hn

lemma cancellation_product :
    (AddMonoidAlgebra.single (0 : ℤ) (1 : ℚ) - AddMonoidAlgebra.single 1 1) *
      (AddMonoidAlgebra.single 0 1 + AddMonoidAlgebra.single 1 1) =
      AddMonoidAlgebra.single 0 1 - AddMonoidAlgebra.single 2 1 := by
  simp only [mul_add, sub_mul, AddMonoidAlgebra.single_mul_single]
  norm_num

lemma stencil_impulse [DecidableEq G] (p : AddMonoidAlgebra K G) (a : G) :
    stencilAct p (fun y => if y = a then 1 else 0) 0 = p.coeff a := by
  classical
  by_cases ha : p.coeff a = 0 <;>
    simp [stencilAct, Finsupp.sum, mul_ite, Finsupp.mem_support_iff, ha]

lemma stencilAct_injective : Function.Injective (stencilAct (K := K) (G := G)) := by
  classical
  intro p q h
  ext a
  have he := congrArg (fun F => F (fun y => if y = a then 1 else 0) 0) h
  simpa only [stencil_impulse] using he

lemma strict_stencil_support : ∃ p q : AddMonoidAlgebra ℚ ℤ,
    1 ∈ p.coeff.support + q.coeff.support ∧ 1 ∉ (p * q).coeff.support := by
  let p : AddMonoidAlgebra ℚ ℤ := AddMonoidAlgebra.single 0 1 - AddMonoidAlgebra.single 1 1
  let q : AddMonoidAlgebra ℚ ℤ := AddMonoidAlgebra.single 0 1 + AddMonoidAlgebra.single 1 1
  have hp0 : p.coeff 0 = 1 := by
    change ((Finsupp.single (0 : ℤ) (1 : ℚ) - Finsupp.single 1 1) : ℤ →₀ ℚ) 0 = 1
    simp
  have hq1 : q.coeff 1 = 1 := by
    change ((Finsupp.single (0 : ℤ) (1 : ℚ) + Finsupp.single 1 1) : ℤ →₀ ℚ) 1 = 1
    simp
  have hprod : p * q = AddMonoidAlgebra.single 0 1 - AddMonoidAlgebra.single 2 1 :=
    cancellation_product
  refine ⟨p, q, ?_, ?_⟩
  · exact Finset.mem_add.mpr ⟨0, by simp [Finsupp.mem_support_iff, hp0],
      1, by simp [Finsupp.mem_support_iff, hq1], by norm_num⟩
  · rw [hprod]
    change 1 ∉ (Finsupp.single (0 : ℤ) (1 : ℚ) - Finsupp.single 2 1).support
    simp [Finsupp.mem_support_iff]

/-- **GAC:stencil-support** (global support and restricted-field agreement differ). -/
@[ledger "GAC:stencil-support"]
theorem stencilSupport : Statement.stencilSupport := by
  refine ⟨?_, ?_, ?_, strict_stencil_support⟩
  · intro K G _ _ _
    exact ⟨stencilAct_mul, stencilAct_injective, stencil_support_mul⟩
  · intro K _ d p q r s hp hq
    exact stencil_radius_mul p q r s hp hq
  · intro n
    exact ⟨averaging_constant n, averaging_dense n⟩

/-! ## Non-vacuity -/

example : averagingMatrix 1 0 1 = 1 / 2 ∧
    (1 : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = 0 := by norm_num [averagingMatrix]

example :
    HasStencilRadius (AddMonoidAlgebra.single (fun _ : Fin 1 => (1 : ℤ)) (1 : ℚ)) 1 ∧
    ¬ HasStencilRadius ((AddMonoidAlgebra.single (fun _ : Fin 1 => (1 : ℤ)) (1 : ℚ)) ^ 2) 1 := by
  constructor
  · intro a ha i
    have he : a = (fun _ : Fin 1 => (1 : ℤ)) := by
      simpa [Finsupp.mem_support_iff] using ha
    subst a
    simp
  · intro h
    have hs : (fun _ : Fin 1 => (2 : ℤ)) ∈
        ((AddMonoidAlgebra.single (fun _ : Fin 1 => (1 : ℤ)) (1 : ℚ)) ^ 2).coeff.support := by
      simp only [AddMonoidAlgebra.single_pow, nsmul_eq_mul, Nat.cast_ofNat, one_pow,
        AddMonoidAlgebra.coeff_single, ne_eq, one_ne_zero, not_false_eq_true,
        Finsupp.support_single, Finset.mem_singleton]
      ext i
      norm_num
    have hx := h _ hs 0
    norm_num at hx

example (p q : AddMonoidAlgebra ℚ ℤ) :
    (realize [Step.kick p, Step.move q] :
      Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra ℚ ℤ)) 0 0 = 1 + q * p := by
  simp [realize, Step.mat, Matrix.SpecialLinearGroup.coe_mul]

end Artform.Scores.GravityBridge
