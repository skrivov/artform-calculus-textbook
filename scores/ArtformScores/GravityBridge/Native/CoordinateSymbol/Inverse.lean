import ArtformScores.GravityBridge.Native.CoordinateSymbol.InverseStatements

/-! # Original coordinate symbol and guarded two-sided inverse -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix

variable {K : Type*} [Field K] [CharZero K]

open Matrix
omit [CharZero K] in
lemma two_value_products (C : Mat4 (K := K)) (d a b : K) (hC : C * C = d • C) :
    twoValueSymbol C d a b * twoValueNumerator C d a b = (a * b * d ^ 2) • 1 ∧
    twoValueNumerator C d a b * twoValueSymbol C d a b = (a * b * d ^ 2) • 1 := by
  constructor
  · simp only [twoValueSymbol, twoValueNumerator, add_mul, mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul]
    rw [hC]
    module
  · simp only [twoValueSymbol, twoValueNumerator, add_mul, mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul]
    rw [hC]
    module

omit [CharZero K] in
lemma two_value_inverse_both (C : Mat4 (K := K)) (d a b : K) (hC : C * C = d • C)
    (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    twoValueSymbol C d a b * twoValueInverse C d a b = 1 ∧
    twoValueInverse C d a b * twoValueSymbol C d a b = 1 := by
  have hn : a * b * d ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) (pow_ne_zero _ hd)
  constructor
  · rw [twoValueInverse, Matrix.mul_smul, (two_value_products C d a b hC).1,
      smul_smul, inv_mul_cancel₀ hn, one_smul]
  · rw [twoValueInverse, Matrix.smul_mul, (two_value_products C d a b hC).2,
      smul_smul, inv_mul_cancel₀ hn, one_smul]

omit [CharZero K] in
lemma eta_matrix_square : etaMatrix (K := K) * etaMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [etaMatrix, signature, Matrix.mul_apply, Fin.sum_univ_succ]

omit [CharZero K] in
lemma original_raised_basis (u p : Vec4 (K := K)) :
    raisedK u p = etaMatrix * lorentzK u p := by
  ext i j
  simp [etaMatrix, Matrix.diagonal_mul, raisedK]

omit [CharZero K] in
lemma native_upper_symbol_factor (p : Vec4 (K := K)) :
    nativeUpperSymbol p = (2 / 101 : K) •
      (etaMatrix * twoValueSymbol (raisedK (componentSquares p) p)
        (simpleDiscriminant (componentSquares p) p) (9999 / 9991) (10201 / 10300)) := by
  rw [nativeUpperSymbol, twoValueSymbol, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, original_raised_basis, ← Matrix.mul_assoc, eta_matrix_square, Matrix.one_mul]
  rfl

lemma native_coordinate_both_inverse (p : Vec4 (K := K))
    (hd : simpleDiscriminant (componentSquares p) p ≠ 0) :
    nativeUpperSymbol p * nativeCoordinateInverse p = 1 ∧
    nativeCoordinateInverse p * nativeUpperSymbol p = 1 := by
  have hC := original_simple_bivector_relation (componentSquares p) p
  have hi := two_value_inverse_both (raisedK (componentSquares p) p)
    (simpleDiscriminant (componentSquares p) p) (9999 / 9991) (10201 / 10300) hC hd
      (by norm_num) (by norm_num)
  constructor
  · rw [native_upper_symbol_factor, nativeCoordinateInverse, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    norm_num
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (twoValueSymbol _ _ _ _) (twoValueInverse _ _ _ _),
      hi.1, Matrix.one_mul, eta_matrix_square]
  · rw [native_upper_symbol_factor, nativeCoordinateInverse, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    norm_num
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc etaMatrix etaMatrix, eta_matrix_square, Matrix.one_mul]
    exact hi.2

lemma native_lower_two_sided (p : Vec4 (K := K))
    (hd : simpleDiscriminant (componentSquares p) p ≠ 0) :
    nativeLowerSymbol p * nativeLowerInverse p = 1 ∧
    nativeLowerInverse p * nativeLowerSymbol p = 1 := by
  have hi := native_coordinate_both_inverse p hd
  constructor
  · simp only [nativeLowerSymbol, nativeLowerInverse, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc etaMatrix etaMatrix, eta_matrix_square, Matrix.one_mul,
      ← Matrix.mul_assoc (nativeUpperSymbol p) (nativeCoordinateInverse p), hi.1,
      Matrix.one_mul, eta_matrix_square]
  · simp only [nativeLowerSymbol, nativeLowerInverse, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc etaMatrix etaMatrix, eta_matrix_square, Matrix.one_mul,
      ← Matrix.mul_assoc (nativeCoordinateInverse p) (nativeUpperSymbol p), hi.2,
      Matrix.one_mul, eta_matrix_square]

/-- **GAC2:native-coordinate-two-sided-inverse**
(original coordinate symbol and guarded two-sided inverse). -/
@[ledger "GAC2:native-coordinate-two-sided-inverse"]
theorem inverseLaw : Statement.inverseLaw := by
  intro K _ _
  exact ⟨two_value_products,
    two_value_inverse_both,
    native_coordinate_both_inverse,
    native_lower_two_sided⟩

/-! ## Non-vacuity -/

example : nativeUpperSymbol (![1, 2, 3, 4] : Vec4 (K := ℚ)) *
    nativeCoordinateInverse ![1, 2, 3, 4] = 1 := by
  apply (native_coordinate_both_inverse ![1, 2, 3, 4] ?_).1
  norm_num [simpleDiscriminant, lorentzDot, componentSquares, signature, Fin.sum_univ_succ]

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
