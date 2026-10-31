import ArtformScores.GravityBridge.Native.InverseJets.ThirdStatements

/-! # Ordered noncommutative inverse jets through third order -/

namespace Artform.Scores.GravityBridge.Native.InverseJets

open Matrix

variable {R : Type*} [Ring R]

lemma ordered_inverse_right (N0 N1 N2 N3 H : R) (hNH : N0 * H = 1) :
    N0 * inverseJet1 H N1 + N1 * H = 0 ∧
    N0 * inverseJet2 H N1 N2 + N1 * inverseJet1 H N1 + N2 * H = 0 ∧
    N0 * inverseJet3 H N1 N2 N3 + N1 * inverseJet2 H N1 N2 +
      N2 * inverseJet1 H N1 + N3 * H = 0 := by
  simp only [inverseJet1, inverseJet2, inverseJet3, mul_add, mul_sub, mul_neg,
    ← mul_assoc, hNH, one_mul]
  refine ⟨neg_add_cancel _, ?_, ?_⟩ <;> noncomm_ring

lemma ordered_inverse_left (N0 N1 N2 N3 H : R) (hHN : H * N0 = 1) :
    inverseJet1 H N1 * N0 + H * N1 = 0 ∧
    inverseJet2 H N1 N2 * N0 + inverseJet1 H N1 * N1 + H * N2 = 0 ∧
    inverseJet3 H N1 N2 N3 * N0 + inverseJet2 H N1 N2 * N1 +
      inverseJet1 H N1 * N2 + H * N3 = 0 := by
  simp only [inverseJet1, inverseJet2, inverseJet3, add_mul, sub_mul, neg_mul,
    mul_assoc, hHN, mul_one]
  refine ⟨neg_add_cancel _, ?_, ?_⟩ <;> noncomm_ring

-- Noncommuting coefficient uniqueness: a left inverse suffices for right recurrences.
lemma inverse_third_unique (N0 N1 N2 N3 H X : R) (hHN : H * N0 = 1)
    (hNH : N0 * H = 1)
    (hx : N0 * X + N1 * inverseJet2 H N1 N2 + N2 * inverseJet1 H N1 + N3 * H = 0) :
    X = inverseJet3 H N1 N2 N3 := by
  have ht := (ordered_inverse_right N0 N1 N2 N3 H hNH).2.2
  have he : N0 * X = N0 * inverseJet3 H N1 N2 N3 := by
    exact add_right_cancel (show N0 * X + (N1 * inverseJet2 H N1 N2 +
      N2 * inverseJet1 H N1 + N3 * H) = N0 * inverseJet3 H N1 N2 N3 +
      (N1 * inverseJet2 H N1 N2 + N2 * inverseJet1 H N1 + N3 * H) from
      by simpa only [add_assoc] using hx.trans ht.symm)
  have hh := congrArg (fun z => H * z) he
  simpa only [← mul_assoc, hHN, one_mul] using hh

-- The native incoming link inverse has the opposite cubic coefficient.
lemma native_ordered_third_identity (l p q : ℚ) :
    signedN0 * thirdH l p q + firstN l p q * secondH l p q +
      secondN l p q * firstH l p q + thirdN l p q * signedH0 = 0 := by
  exact (ordered_inverse_right _ _ _ _ _ signed_zero_inverse.1).2.2


lemma link_cube_diagonal (l p q : ℚ) :
    linkCube l p q = (1 / 4 : ℚ) • linkD (l ^ 3) (p ^ 3) (q ^ 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [linkCube, linkD, Matrix.mul_apply, Matrix.diagonal_apply,
      Fin.sum_univ_succ, Matrix.one_apply] <;> ring

lemma native_third_link_product (l p q : ℚ) : thirdN l p q = thirdLinkProduct l p q := by
  rw [thirdLinkProduct, link_cube_diagonal]
  simp only [thirdN, firstN, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, smul_smul, ← Matrix.mul_assoc]
  module

/-- **GAC2:ordered-third-inverse-jets**
(ordered noncommutative inverse jets through third order). -/
@[ledger "GAC2:ordered-third-inverse-jets"]
theorem thirdLaw : Statement.thirdLaw := by
  intro R _
  exact ⟨ordered_inverse_right,
    ordered_inverse_left,
    inverse_third_unique,
    native_ordered_third_identity,
    link_cube_diagonal,
    native_third_link_product⟩

/-! ## Non-vacuity -/

-- The two mixed orderings matter on actual matrices; dropping either changes the answer.
example : let H : Matrix (Fin 2) (Fin 2) ℚ := 1
    let N1 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1;0, 0]
    let N2 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0;1, 0]
    inverseJet3 H N1 N2 0 = 1 ∧ N1 * N2 ≠ N2 * N1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [inverseJet3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  · intro h
    have hh := congrFun (congrFun h 0) 0
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at hh

end Artform.Scores.GravityBridge.Native.InverseJets
