import ArtformScores.GravityBridge.Native.InverseJets.SignedStatements
/-! # Original signed physical block and ordered inverse contacts -/
namespace Artform.Scores.GravityBridge.Native.InverseJets
open Matrix
open Full40
open Retrospective
open Matrix
open Full40
open Retrospective
lemma original_signed_torsion (z : Fin 3 → ℚ) :
    physicalTorsionRows z = signedC *ᵥ z := by
  ext i
  fin_cases i <;> norm_num [physicalTorsionRows, physicalConnection, torsion, lie, wedge,
    basisVector, signedC, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.vecMul,
      Matrix.transpose_apply, Matrix.diagonal_apply,
    vecHead, vecTail, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply]
lemma original_basis_conversion (z : Fin 3 → ℚ) :
    -physicalConnection z = distinctInput 0 ![-z 0, z 1, -z 2] := by
  ext i a
  fin_cases i <;> fin_cases a <;>
    norm_num [physicalConnection, distinctInput, distinctIndices, wedge, basisVector,
      Fin.sum_univ_succ, Matrix.vecMul, Matrix.transpose_apply, Matrix.diagonal_apply,
    vecHead, vecTail, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply]
lemma signed_zero_inverse :
    signedN0 * signedH0 = 1 ∧ signedH0 * signedN0 = 1 ∧
    signedBc * signedBcInverse = 1 ∧ signedC *ᵥ signedV = (-2 : ℚ) • signedW := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
    norm_num [signedN0, signedH0, signedBc, signedBcInverse, rankOne, signedV, signedW,
    signedC, signedAlpha, signedA, signedE, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.vecMul, Matrix.transpose_apply, Matrix.diagonal_apply,
    vecHead, vecTail, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
    norm_num [signedN0, signedH0, signedBc, signedBcInverse, rankOne, signedV, signedW,
    signedC, signedAlpha, signedA, signedE, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.vecMul, Matrix.transpose_apply, Matrix.diagonal_apply,
    vecHead, vecTail, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
    norm_num [signedN0, signedH0, signedBc, signedBcInverse, rankOne, signedV, signedW,
    signedC, signedAlpha, signedA, signedE, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.vecMul, Matrix.transpose_apply, Matrix.diagonal_apply,
    vecHead, vecTail, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply]
  · ext i
    fin_cases i <;>
    norm_num [signedN0, signedH0, signedBc, signedBcInverse, rankOne, signedV, signedW,
    signedC, signedAlpha, signedA, signedE, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.vecMul, Matrix.transpose_apply, Matrix.diagonal_apply,
    vecHead, vecTail, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply]
lemma first_native_numerator (l p q : ℚ) :
    firstN l p q = (1/101 : ℚ) • !![0, q-p, q-l;p-q, 0, l-p;l-q, p-l, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstN, signedC, linkD, signedBcInverse, rankOne, signedV,
      Matrix.mul_apply, Matrix.vecMul, Matrix.transpose_apply, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      vecHead, vecTail, Fin.sum_univ_succ] <;> ring
-- Finite rational matrix products retain all ordered inverse contacts.
set_option maxHeartbeats 1600000 in
-- Exact finite rational matrix products need a larger elaboration budget.
lemma first_inverse_table (l p q : ℚ) :
    firstH l p q = (1/101 * signedG * signedA : ℚ) •
      !![0, p-q, l-q;q-p, 0, p-l;q-l, l-p, 0] := by
  rw [firstH, first_native_numerator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstH, firstN, signedH0, signedC, linkD, signedBcInverse, rankOne,
      signedV, signedW, signedA, signedE, signedG, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.vecMul, Matrix.transpose_apply, Matrix.diagonal_apply,
    vecHead, vecTail, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply] <;> ring
lemma second_native_numerator (l p q : ℚ) : secondN l p q = sourceN2 l p q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondN, sourceN2, sourceL, signedC, linkD, signedBcInverse, rankOne, signedV,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, Matrix.transpose_apply,
        Matrix.diagonal_apply,
    vecHead, vecTail, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply] <;> ring
-- Ordered inverse identities: no commutation of either N1 or N2 with H0.
lemma first_inverse_identity (l p q : ℚ) :
    signedN0 * firstH l p q + firstN l p q * signedH0 = 0 := by
  rw [firstH, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    signed_zero_inverse.1, Matrix.one_mul]
  simp
lemma second_inverse_identity (l p q : ℚ) :
    signedN0 * secondH l p q + firstN l p q * firstH l p q +
      secondN l p q * signedH0 = 0 := by
  simp only [secondH, firstH, Matrix.mul_sub, Matrix.mul_neg]
  simp only [← Matrix.mul_assoc, signed_zero_inverse.1, Matrix.one_mul]
  abel
-- The contact uses the full two ordered inverse products.
set_option maxHeartbeats 1600000 in
-- Exact finite rational matrix products need a larger elaboration budget.
lemma second_temporal_contact (x y : ℚ) :
    (secondH 1 0 0 *ᵥ ![x, y, 0]) 2 =
      ((1/101 : ℚ)^2 * signedA^2 * signedG) * (x-y) := by
  norm_num [secondH, firstN, secondN, signedH0, signedC, linkD, signedBcInverse, rankOne,
    signedV, signedW, signedA, signedE, signedG, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.vecMul, Matrix.transpose_apply, Matrix.diagonal_apply,
    vecHead, vecTail, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply]
  ring
-- Inclusion-exclusion extracts the two mixed monomials of this quadratic jet.
-- The two finite mixed-jet extractions are checked by exact rational arithmetic.
set_option maxHeartbeats 1600000 in
-- Exact finite rational matrix products need a larger elaboration budget.
lemma second_mixed_contacts :
    ((secondH 1 1 0 - secondH 1 0 0 - secondH 0 1 0) *ᵥ ![1, 1, 0]) 2 =
      (1/101 : ℚ)^2 * signedA^2 * signedG ∧
    ((secondH 1 0 1 - secondH 1 0 0 - secondH 0 0 1) *ᵥ ![1, 1, 0]) 2 =
      -(1/101 : ℚ)^2 * signedA^2 * signedG := by
  norm_num [secondH, firstN, secondN, signedH0, signedC, linkD, signedBcInverse, rankOne,
    signedV, signedW, signedA, signedE, signedG, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.vecMul, Matrix.transpose_apply, Matrix.diagonal_apply,
    vecHead, vecTail, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply]
/-- **GAC2:signed-ordered-inverse-contacts**
(original signed physical block and ordered inverse contacts). -/
@[ledger "GAC2:signed-ordered-inverse-contacts"]
theorem signedLaw : Statement.signedLaw := by
  
  exact ⟨original_signed_torsion,
    original_basis_conversion,
    signed_zero_inverse,
    first_native_numerator,
    first_inverse_table,
    second_native_numerator,
    first_inverse_identity,
    second_inverse_identity,
    second_temporal_contact,
    second_mixed_contacts⟩
/-! ## Non-vacuity -/
example : (physicalTorsionRows ![1, 2, 3]) 0 = -3 ∧
    (firstH 1 2 3) 0 1 = -101/9991 ∧
    (secondH 1 0 0 *ᵥ ![1, 0, 0]) 2 ≠ 0 := by
  rw [original_signed_torsion, first_inverse_table, second_temporal_contact]
  norm_num [signedC, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, signedG, signedA]
end Artform.Scores.GravityBridge.Native.InverseJets
