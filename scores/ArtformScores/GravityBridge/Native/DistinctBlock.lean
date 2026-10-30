import ArtformScores.GravityBridge.Native.Statements

/-! # The native signed distinct block cancels its spatial-face component -/

namespace Artform.Scores.GravityBridge.Native

open Matrix

theorem connectionBlock_det : connectionBlock.det = 2058146 / 1030301 := by
  norm_num [connectionBlock, curvatureBlock, kappa, torsionBlock, facePairing,
    Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_succ]

theorem connectionBlock_det_ne_zero : connectionBlock.det ≠ 0 := by
  rw [connectionBlock_det]
  norm_num

theorem schurCovector_eq (z : ℚ) :
    schurCovector z = ![-101 * z / 103, -101 * z / 103, 0] := by
  let r : Fin 3 → ℚ := ![0, -z, z]
  let w : Fin 3 → ℚ := ![0, 101 * z / 103, -101 * z / 103]
  have hr : (torsionBlock.transpose * facePairing) *ᵥ faceInput z = r := by
    ext i
    fin_cases i <;>
      simp [r, torsionBlock, facePairing, faceInput, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hw : connectionBlock *ᵥ w = r := by
    ext i
    fin_cases i <;>
      norm_num [w, r, connectionBlock, curvatureBlock, kappa, torsionBlock,
        facePairing, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] <;> ring
  have hinv : connectionBlock⁻¹ *ᵥ r = w := by
    rw [← hw, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr connectionBlock_det_ne_zero),
      Matrix.one_mulVec]
  unfold schurCovector
  rw [hr, hinv]
  ext i
  fin_cases i <;>
    norm_num [w, kappa, facePairing, torsionBlock, faceInput, Matrix.mul_apply,
      Matrix.mulVec, Matrix.one_apply, dotProduct, Fin.sum_univ_succ] <;> ring

/-- **GAC:native-distinct-block** (the signed native Schur cancellation). -/
@[ledger "GAC:native-distinct-block"]
theorem distinctBlock : Statement.distinctBlock :=
  ⟨connectionBlock_det, schurCovector_eq⟩

/-! ## Non-vacuity -/

/-- A nonzero Christoffel input has zero spatial-face Schur output. -/
example : faceInput 1 ≠ 0 ∧ schurCovector 1 2 = 0 := by
  constructor
  · intro h
    have hi := congrFun h 0
    norm_num [faceInput] at hi
  · rw [schurCovector_eq]
    norm_num

end Artform.Scores.GravityBridge.Native
