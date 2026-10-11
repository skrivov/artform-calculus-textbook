import ArtformTextbook.Ch12.ModelsCheck2

/-!
# The operators of the models on the product bases

The kernel's checks of `Ch12/ModelsCheck.lean` and `Ch12/ModelsCheck2.lean`, read in `ℂ`: each
operator carries a combination of products `Σ a_j B_j` to `Σ (K a)_i B_i`, `K` the matrix of its
columns in the certificate.
-/

namespace Artform.ModelsCheck

open scoped Matrix

open FockCalc ModelsData Edge SpecCert

/-- The parity rule `parB` is `below`. -/
theorem parB_spec (k i : ℕ) : parB k i = (below k i % 2 == 1) := rfl

theorem toFock_combo_basis {n : ℕ} (hn0 : 0 < n) (bv : ℕ → Vec)
    (B : Fin n → Finset EM → ℂ) (hB : ∀ j : Fin n, B j = Vec.toFock code (bv j)) (col : Vec)
    (hk : keysLt n col = true) :
    Vec.toFock code (Vec.combo (col.map fun p => (p.2, bv p.1))) =
      (col.map fun p => (p.2 : ℂ) • B ⟨p.1 % n, Nat.mod_lt _ hn0⟩).sum := by
  rw [Vec.toFock_combo, List.map_map]
  apply congrArg List.sum
  refine List.map_congr_left fun p hp => ?_
  simp only [keysLt, List.all_eq_true, decide_eq_true_eq] at hk
  simp only [Function.comp_apply, hB, Nat.mod_eq_of_lt (hk p hp)]

/-- An operator of words, checked column by column on a basis of products. -/
theorem op_lc {n d : ℕ} (hn : n ≤ 2 ^ d) (hn0 : 0 < n) (O : Op EM)
    (X : Matrix (Finset EM) (Finset EM) ℂ) (hO : Op.toMat bookOrd O = X) (cols : List Vec)
    (bv : ℕ → Vec) (B : Fin n → Finset EM → ℂ) (hB : ∀ j : Fin n, B j = Vec.toFock code (bv j))
    (hk : ∀ j : Fin n, keysLt n (cols.getD j []) = true)
    (hc : ∀ j : Fin n, colCheck (O.compile code) cols bv j = true) (a : Fin n → ℂ) :
    X *ᵥ Fintype.linearCombination ℂ B a =
      Fintype.linearCombination ℂ B (colMat d n cols *ᵥ a) := by
  refine mulVec_linearCombination hn hn0 X B cols hk (fun j => ?_) a
  rw [hB, ← hO, Op.toMat_mulVec_compile numbering parB parB_spec,
    Vec.toFock_eq_of_trie_eq numbering (by simpa only [colCheck, beq_iff_eq] using hc j),
    toFock_combo_basis hn0 bv B hB _ (hk j)]

/-- A diagonal operator read off the masks, checked column by column on a basis of products. -/
theorem diag_lc {n d : ℕ} (hn : n ≤ 2 ^ d) (hn0 : 0 < n) (dfun : Finset EM → ℂ) (f : ℕ → ℤ)
    (hf : ∀ k, dfun (decode code k) = f k) (cols : List Vec)
    (bv : ℕ → Vec) (B : Fin n → Finset EM → ℂ) (hB : ∀ j : Fin n, B j = Vec.toFock code (bv j))
    (hk : ∀ j : Fin n, keysLt n (cols.getD j []) = true)
    (hc : ∀ j : Fin n, diagCheck f cols bv j = true) (a : Fin n → ℂ) :
    Matrix.diagonal dfun *ᵥ Fintype.linearCombination ℂ B a =
      Fintype.linearCombination ℂ B (colMat d n cols *ᵥ a) := by
  refine mulVec_linearCombination hn hn0 _ B cols hk (fun j => ?_) a
  rw [hB, diagonal_mulVec_toFock dfun f hf,
    Vec.toFock_eq_of_trie_eq numbering (by simpa only [diagCheck, beq_iff_eq] using hc j),
    toFock_combo_basis hn0 bv B hB _ (hk j)]

theorem all_range_iff (P : ℕ → Bool) (n : ℕ) :
    (List.range n).all P = true ↔ ∀ j < n, P j = true := by
  simp [List.all_eq_true, List.mem_range]

/-! ### `3 Ω` -/

theorem omega1_keys : ∀ j : Fin 64, keysLt 64 (omega1Cols.getD j []) = true := by decide

theorem omega0_keys : ∀ j : Fin 64, keysLt 64 (omega0Cols.getD j []) = true := by decide

theorem omega36_keys : ∀ j : Fin 36, keysLt 36 (omega36Cols.getD j []) = true := by decide

theorem tally3Op_one : Op.toMat bookOrd (tally3Op 1) = (3 : ℂ) • tally bookOrd 1 := by
  simpa using tally3Op_toMat 1

theorem tally3Op_zero : Op.toMat bookOrd (tally3Op 0) = (3 : ℂ) • tally bookOrd 0 := by
  simpa using tally3Op_toMat 0

/-- `3 Ω` with the pair hop on the sixty-four products. -/
theorem omega1_lc (a : Fin 64 → ℂ) :
    ((3 : ℂ) • tally bookOrd 1) *ᵥ Φ64 a = Φ64 (colMat 6 64 omega1Cols *ᵥ a) :=
  op_lc (d := 6) (by norm_num) (by norm_num) (tally3Op 1) _ tally3Op_one omega1Cols basisVec
    B64 B64_eq omega1_keys (fun j => omega1_cols j j.2) a

/-- `3 Ω` without the pair hop on the sixty-four products. -/
theorem omega0_lc (a : Fin 64 → ℂ) :
    ((3 : ℂ) • tally bookOrd 0) *ᵥ Φ64 a = Φ64 (colMat 6 64 omega0Cols *ᵥ a) :=
  op_lc (d := 6) (by norm_num) (by norm_num) (tally3Op 0) _ tally3Op_zero omega0Cols basisVec
    B64 B64_eq omega0_keys (fun j => omega0_cols j j.2) a

/-- `3 Ω` without the pair hop on the thirty-six products of the six. -/
theorem omega36_lc (a : Fin 36 → ℂ) :
    ((3 : ℂ) • tally bookOrd 0) *ᵥ Φ36 a = Φ36 (colMat 6 36 omega36Cols *ᵥ a) :=
  op_lc (d := 6) (by norm_num) (by norm_num) (tally3Op 0) _ tally3Op_zero omega36Cols basisVec36
    B36 B36_eq omega36_keys (fun j => omega36_cols j (by omega)) a

end Artform.ModelsCheck
