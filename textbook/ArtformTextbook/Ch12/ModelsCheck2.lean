import ArtformTextbook.Ch12.ModelsCheck
import ArtformTextbook.Ch12.SpectrumJoint

/-!
# The kernel's checks of the certificate: spin, the hole map and the parity

On the sixteen products of two quartets, the columns of `3 Ω`, `2 S_z` and `4 S²`, and their common
eigenvectors; on the sixty-four products, the columns of the hole map `𝒮` and of the parity
`(-1)^{N_x}`.
-/

namespace Artform.ModelsCheck

open scoped Matrix

open FockCalc ModelsData Edge SpecCert

/-- `S₊ S₋ + S₋ S₊`, compiled. -/
def spinPMC : OpC := (Op.mul spinPlusOp spinMinusOp ++ Op.mul spinMinusOp spinPlusOp).compile code

/-- The image of the product of two quartets `l` under `4 S² = (2 S_z)² + 2 (S₊ S₋ + S₋ S₊)`. -/
def sqCheck (l : ℕ) : Bool :=
  Vec.trie 12 (((blockVec l).map fun p => (p.1, spinZ2 p.1 * (spinZ2 p.1 * p.2))) ++
      Vec.smul 2 (OpC.act parB spinPMC (blockVec l))) ==
    Vec.trie 12 (Vec.combo ((blockSqCols.getD l []).map fun p => (p.2, blockVec p.1)))

/-- The six factors `a ± a†` of the hole map, compiled. -/
def holeC : OpC := holeWordsOp.compile code

/-- The image of the product `j` under the hole map. -/
def holeCheck (j : ℕ) : Bool :=
  Vec.trie 12 ((OpC.act parB holeC (basisVec j)).map fun p => (p.1, upSignF p.1 * p.2)) ==
    Vec.trie 12 (Vec.combo ((holeCols.getD j []).map fun p => (p.2, basisVec p.1)))

/-- The certificate of the sixteen for the operator in place `r` (`3 Ω`, `2 S_z`, `4 S²`). -/
def blockEigOf (r : ℕ) : List (ℤ × Vec) := blockEig.map fun e => (e.1.getD r 0, e.2)

/-! ### The sixteen products of two quartets -/

theorem block3_cols : (List.range 16).all (colCheck tally1C block3Cols blockVec) = true := by
  decide +kernel

theorem blockSz_cols : (List.range 16).all (diagCheck spinZ2 blockSzCols blockVec) = true := by
  decide +kernel

theorem blockSq_cols : (List.range 16).all sqCheck = true := by
  decide +kernel

theorem block_eig3 : eigOK 4 16 block3Cols (blockEigOf 0) = true := by decide +kernel

theorem block_eigSz : eigOK 4 16 blockSzCols (blockEigOf 1) = true := by decide +kernel

theorem block_eigSq : eigOK 4 16 blockSqCols (blockEigOf 2) = true := by decide +kernel

theorem block_inv : invOK 4 16 blockD (blockEigOf 0) blockDg = true := by decide +kernel

/-! ### The hole map and the parity -/

theorem hole_cols_0 : (List.range' 0 32).all holeCheck = true := by decide +kernel

theorem hole_cols_1 : (List.range' 32 32).all holeCheck = true := by decide +kernel

theorem parity_cols : (List.range 64).all (diagCheck parityF parityCols basisVec) = true := by
  decide +kernel

end Artform.ModelsCheck
