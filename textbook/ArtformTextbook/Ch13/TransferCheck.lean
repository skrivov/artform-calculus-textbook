import ArtformTextbook.Ch13.TransferCalc
import ArtformTextbook.Ch13.TransferData

/-!
# The kernel's checks of the transfer certificate

`6 L`, applied by the kernel to each product of the basis (`TransferCheck.colCheckT`), gives the
combination of products listed in the certificate `Ch13/TransferData.lean`; read in `ℂ`, `6 L`
carries every combination of products to the combination given by the matrix of the columns
(`TransferCheck.transferR_lc`, `TransferCheck.transferC_lc`). The common eigenvectors of the
number of quarks and of `6 L` (real triplets) or `(6 L)²` (complex triplets) are checked by
`SpecCert.eigOK` and `SpecCert.invOK`, and the action of `6 L` on the named states of Theorem 13.9
directly on their lists.
-/

namespace Artform

open scoped Matrix

open Module FockCalc ModelsData SpecCert ModelsCheck Edge TransferCalc TransferData

namespace TransferCheck

/-- The image of the product `j` under `6 L` is the combination of the column `j`. -/
def colCheckT (real : Bool) (cols : List Vec) (bv : ℕ → Vec) (j : ℕ) : Bool :=
  Vec.trie 12 (transfer6 real (bv j)) ==
    Vec.trie 12 (Vec.combo ((cols.getD j []).map fun p => (p.2, bv p.1)))

/-! ### The columns of `6 L` for a real triplet -/

set_option maxRecDepth 100000 in
theorem transferR_cols_0 :
    (List.range' 0 8).all (colCheckT true transferRCols basisVec) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem transferR_cols_1 :
    (List.range' 8 8).all (colCheckT true transferRCols basisVec) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem transferR_cols_2 :
    (List.range' 16 8).all (colCheckT true transferRCols basisVec) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem transferR_cols_3 :
    (List.range' 24 8).all (colCheckT true transferRCols basisVec) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem transferR_cols_4 :
    (List.range' 32 8).all (colCheckT true transferRCols basisVec) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem transferR_cols_5 :
    (List.range' 40 8).all (colCheckT true transferRCols basisVec) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem transferR_cols_6 :
    (List.range' 48 8).all (colCheckT true transferRCols basisVec) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem transferR_cols_7 :
    (List.range' 56 8).all (colCheckT true transferRCols basisVec) = true := by decide +kernel

theorem transferR_cols : ∀ j < 64, colCheckT true transferRCols basisVec j = true :=
  all_range_of_chunks _ 8 8 fun a ha => by
    interval_cases a
    · exact transferR_cols_0
    · exact transferR_cols_1
    · exact transferR_cols_2
    · exact transferR_cols_3
    · exact transferR_cols_4
    · exact transferR_cols_5
    · exact transferR_cols_6
    · exact transferR_cols_7

/-! ### The columns of `6 L` for a complex triplet -/

set_option maxRecDepth 100000 in
theorem transferC_cols_0 :
    (List.range' 0 9).all (colCheckT false transferCCols basisVec36) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem transferC_cols_1 :
    (List.range' 9 9).all (colCheckT false transferCCols basisVec36) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem transferC_cols_2 :
    (List.range' 18 9).all (colCheckT false transferCCols basisVec36) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem transferC_cols_3 :
    (List.range' 27 9).all (colCheckT false transferCCols basisVec36) = true := by decide +kernel

theorem transferC_cols : ∀ j < 36, colCheckT false transferCCols basisVec36 j = true :=
  all_range_of_chunks _ 9 4 fun a ha => by
    interval_cases a
    · exact transferC_cols_0
    · exact transferC_cols_1
    · exact transferC_cols_2
    · exact transferC_cols_3

/-! ### The certificates -/

/-- The number of quarks on the sixty-four products, by columns. -/
def numCols64 : List Vec := (List.range 64).map fun j => [(j, ((nq (j / 8) + nq (j % 8) : ℕ) : ℤ))]

/-- The number of quarks on the thirty-six products of the six, by columns. -/
def numCols36 : List Vec :=
  (List.range 36).map fun j => [(j, ((nq (Vertex.sixToEight ⟨j / 6 % 6, Nat.mod_lt _
    (by norm_num)⟩) + nq (Vertex.sixToEight ⟨j % 6, Nat.mod_lt _ (by norm_num)⟩) : ℕ) : ℤ))]

/-- The number of quarks of a mask. -/
def numF (k : ℕ) : ℤ := ((decode code k).card : ℤ)

theorem numR_cols : (List.range 64).all (diagCheck numF numCols64 basisVec) = true := by
  decide +kernel

theorem numC_cols : (List.range 36).all (diagCheck numF numCols36 basisVec36) = true := by
  decide +kernel

/-- The values of the real certificate: the number of quarks (`r = 0`) and `6 L` (`r = 1`). -/
def eigR (r : ℕ) : List (ℤ × Vec) := transferREig.map fun e => (e.1.getD r 0, e.2)

/-- The values of the complex certificate: the number of quarks (`r = 0`) and `(6 L)²`
(`r = 1`). -/
def eigC (r : ℕ) : List (ℤ × Vec) := transferCEig.map fun e => (e.1.getD r 0, e.2)

theorem transferR_eig0 : eigOK 6 64 numCols64 (eigR 0) = true := by decide +kernel

theorem transferR_eig1 : eigOK 6 64 transferRCols (eigR 1) = true := by decide +kernel

theorem transferR_inv0 : invOK 6 64 transferRD (eigR 0) transferRDg = true := by decide +kernel

theorem transferC_eig0 : eigOK 6 36 numCols36 (eigC 0) = true := by decide +kernel

theorem transferC_eig1 : eigOK 6 36 transferC2Cols (eigC 1) = true := by decide +kernel

theorem transferC_inv0 : invOK 6 36 transferCD (eigC 0) transferCDg = true := by decide +kernel

/-- The square of the complex columns. -/
theorem transferC2_cols : ∀ j : Fin 36,
    Vec.trie 6 (apply transferCCols (transferCCols.getD j [])) =
      Vec.trie 6 (transferC2Cols.getD j []) := by
  decide +kernel

/-- The vectors of the complex certificate with six quarks and `(6 L)² = 0` are killed by
`6 L`. -/
theorem transferC_null : transferCEig.all (fun e => e.1 != [6, 0] ||
    Vec.trie 6 (apply transferCCols e.2) == Vec.trie 6 []) = true := by
  decide +kernel

theorem keysR : ∀ j : Fin 64, keysLt 64 (transferRCols.getD j []) = true := by decide +kernel

theorem keysC : ∀ j : Fin 36, keysLt 36 (transferCCols.getD j []) = true := by decide +kernel

theorem keysC2 : ∀ j : Fin 36, keysLt 36 (transferC2Cols.getD j []) = true := by decide +kernel

theorem keysN64 : ∀ j : Fin 64, keysLt 64 (numCols64.getD j []) = true := by decide +kernel

theorem keysN36 : ∀ j : Fin 36, keysLt 36 (numCols36.getD j []) = true := by decide +kernel

/-! ### The named states of Theorem 13.9 -/

set_option maxRecDepth 100000 in
theorem quartet_transfer : ∀ m < 4,
    (Vec.trie 12 (transfer6 true (basisVec (8 * (m + 2)))) ==
      Vec.trie 12 (Vec.smul 36 (basisVec (m + 2)))) = true ∧
    (Vec.trie 12 (transfer6 true (basisVec (m + 2))) ==
      Vec.trie 12 (Vec.smul 36 (basisVec (8 * (m + 2))))) = true ∧
    (Vec.trie 12 (transfer6 false (basisVec (8 * (m + 2)))) ==
      Vec.trie 12 (Vec.smul 36 (basisVec (m + 2)))) = true ∧
    (Vec.trie 12 (transfer6 false (basisVec (m + 2))) ==
      Vec.trie 12 (Vec.smul 36 (basisVec (8 * (m + 2))))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem singlet_transfer :
    (Vec.trie 12 (transfer6 false singletVec) ==
      Vec.trie 12 (Vec.combo [(-432, basisVec 56), (-432, basisVec 7)])) = true ∧
    (Vec.trie 12 (transfer6 true singletVec) ==
      Vec.trie 12 (Vec.combo [(-432, basisVec 56), (-432, basisVec 7), (144, basisVec 49),
        (144, basisVec 14)])) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem channel_transfer : ∀ m < 4,
    (Vec.trie 12 (transfer6 true (basisVec (8 + (m + 2)))) ==
      Vec.trie 12 (Vec.smul (-36) (basisVec (8 * (m + 2) + 1)))) = true ∧
    (Vec.trie 12 (transfer6 true (basisVec (48 + (m + 2)))) ==
      Vec.trie 12 (Vec.smul 36 (basisVec (8 * (m + 2) + 6)))) = true := by
  decide +kernel

end TransferCheck

end Artform
