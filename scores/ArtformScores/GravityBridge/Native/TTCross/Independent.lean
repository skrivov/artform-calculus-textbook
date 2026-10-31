import ArtformScores.GravityBridge.Native.TTCross.IndependentStatements

/-! # All24 independent connection residual and native physical sign -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40
lemma original_all24_return_residual (Z : Matrix (Fin 6) (Fin 4) K) :
    fullBApply (independentReturn Z) + (2 / 101 : K) • nativeSourceAdjoint Z = 0 := by
  rw [independentReturn, (original_full24_inverse _).1]
  module

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Resolve the signed permutation on all24 original connection slots.
omit [CharZero K] in
lemma three_connection_scale (c : K) (p m s : Fin 3 → K) :
    c • threeConnection p m s = threeConnection (c • p) (c • m) (c • s) := by
  ext mu a
  fin_cases mu <;> fin_cases a <;>
    simp [threeConnection, gAssemble, gDistinctInput, gRepeatedInput, Retrospective.distinctIndices,
      wedge, basisVector, Fin.sum_univ_succ]

omit [CharZero K] in
lemma full_on_wave_return (j a q v : K) :
    independentReturn (onWaveCrossZ j a q v) =
      threeConnection
        (timeH *ᵥ ((-2 / 101 : K) • (timeT.transpose *ᵥ
          ![(-2 * a ^ 2 * q - j * a * v) / 4, -a ^ 2 * q / 2, j * a * v / 4])))
        (timeH *ᵥ ((-2 / 101 : K) • (timeT.transpose *ᵥ
          ![(-2 * a ^ 2 * q + j * a * v) / 4, -a ^ 2 * q / 2, -j * a * v / 4])))
        (spaceH *ᵥ ((-2 / 101 : K) • (spaceT.transpose *ᵥ
          ![0, -a ^ 2 * q / 2, -a ^ 2 * q / 2]))) := by
  unfold independentReturn onWaveCrossZ
  rw [native_adjoint_three_blocks, three_connection_scale, native_H_three_blocks]

omit [CharZero K] in
lemma native_physical_return_sign (h : K) (hh : h ≠ 0)
    (Z : Matrix (Fin 6) (Fin 4) K) :
    -h • ((-h)⁻¹ • independentReturn Z) = independentReturn Z := by
  rw [smul_smul, mul_inv_cancel₀ (neg_ne_zero.mpr hh), one_smul]

lemma heldout_nonzero_independent_return (j : K) :
    gDistinct (independentReturn (onWaveCrossZ j 1 0 1)) 1 =
      ![-101 * j / 19982, 2 * j / 9991, 101 * j / 19982] := by
  rw [full_on_wave_return]
  unfold threeConnection
  rw [generic_partition_distinct]
  ext i
  fin_cases i <;>
    norm_num [timeT, timeH, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
      Fin.sum_univ_succ] <;> ring

/-- **GAC2:native-full24-independent-return**
(all24 independent connection residual and native physical sign). -/
@[ledger "GAC2:native-full24-independent-return"]
theorem independentLaw : Statement.independentLaw := by
  intro K _ _
  exact ⟨original_all24_return_residual,
    full_on_wave_return,
    native_physical_return_sign,
    heldout_nonzero_independent_return⟩

/-! ## Non-vacuity -/
example : gDistinct (independentReturn (onWaveCrossZ Complex.I 1 0 1)) 1 1 =
    2 * Complex.I / 9991 := by
  rw [heldout_nonzero_independent_return Complex.I]
  rfl

end Artform.Scores.GravityBridge.Native.TTCross
