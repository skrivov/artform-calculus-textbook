import ArtformTextbook.Ch12.ModelsStates

/-!
# The hole map and the parity on the zero-flux sector of Model I

On the sixty-four products the hole map `𝒮` and the parity `(-1)^{N_x}` are the matrices of the
certificate (`ModelsCheck.hole_lc`, `ModelsCheck.parity_lc`), and the kernel checks the relations
`𝒮 Ω = Ω 𝒮`, `P Ω = Ω P` and `𝒮 P = -P 𝒮` among the certificate's matrices, column by column
(`ModelsCheck.colMat_mul_eq_of_check`); read in `ℂ` they hold on the whole sector. Without the
pair hop `𝒮` and `Ω` do not commute on the pair at `y` (`ModelsCheck.hole_tally0_ne`).
-/

namespace Artform

open scoped Matrix

open Module FockCalc ModelsData SpecCert ModelsCheck Edge

namespace ModelsCheck

/-! ### Products of certificate matrices -/

/-- Two products of matrices given by columns agree when, column by column, the combinations do. -/
theorem colMat_mul_eq_of_check {d n : ℕ} (hn : n ≤ 2 ^ d) (A B C E : List Vec)
    (hB : ∀ j : Fin n, keysLt n (B.getD j []) = true)
    (hE : ∀ j : Fin n, keysLt n (E.getD j []) = true)
    (h : ∀ j : Fin n, Vec.trie d (apply A (B.getD j [])) = Vec.trie d (apply C (E.getD j []))) :
    colMat d n A * colMat d n B = colMat d n C * colMat d n E := by
  ext i j
  have hcol : ∀ (X Y : List Vec), (hY : keysLt n (Y.getD j []) = true) →
      (colMat d n X * colMat d n Y) i j = vecFun d n (apply X (Y.getD j [])) i := by
    intro X Y hY
    rw [← colMat_mulVec hn X _ hY]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, vecFun, colMat, Matrix.of_apply]
  rw [hcol A B (hB j), hcol C E (hE j), vecFun_eq_of_trie_eq (h j)]

/-- Two products of matrices given by columns differ by a scalar when, column by column, the
combinations do. -/
theorem colMat_mul_eq_smul_of_check {d n : ℕ} (hn : n ≤ 2 ^ d) (A B C E : List Vec) (c : ℤ)
    (hB : ∀ j : Fin n, keysLt n (B.getD j []) = true)
    (hE : ∀ j : Fin n, keysLt n (E.getD j []) = true)
    (h : ∀ j : Fin n, Vec.trie d (apply A (B.getD j [])) =
      Vec.trie d (Vec.smul c (apply C (E.getD j [])))) :
    colMat d n A * colMat d n B = (c : ℂ) • (colMat d n C * colMat d n E) := by
  ext i j
  have hcol : ∀ (X Y : List Vec), (hY : keysLt n (Y.getD j []) = true) →
      (colMat d n X * colMat d n Y) i j = vecFun d n (apply X (Y.getD j [])) i := by
    intro X Y hY
    rw [← colMat_mulVec hn X _ hY]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, vecFun, colMat, Matrix.of_apply]
  rw [Matrix.smul_apply, hcol A B (hB j), hcol C E (hE j), vecFun_eq_of_trie_eq (h j),
    vecFun_smul, Pi.smul_apply, smul_eq_mul]

theorem all_range'_iff (P : ℕ → Bool) (s n : ℕ) :
    (List.range' s n).all P = true ↔ ∀ j, s ≤ j → j < s + n → P j = true := by
  simp only [List.all_eq_true, List.mem_range'_1, and_imp]

theorem keys_hole : ∀ j : Fin 64, keysLt 64 (holeCols.getD j []) = true := by decide +kernel

theorem keys_parity : ∀ j : Fin 64, keysLt 64 (parityCols.getD j []) = true := by decide +kernel

/-! ### The hole map and the parity on the products -/

theorem holeC_eq : holeC = holeWordsOp.compile code := rfl

/-- `𝒮` on the sixty-four products. -/
theorem hole_lc (a : Fin 64 → ℂ) :
    holeMap bookOrd *ᵥ Φ64 a = Φ64 (colMat 6 64 holeCols *ᵥ a) := by
  refine mulVec_linearCombination (d := 6) (by norm_num) (by norm_num) _ B64 holeCols keys_hole
    (fun j => ?_) a
  rw [B64_eq, holeMap_toFock]
  have hc : holeCheck j = true := by
    rcases Nat.lt_or_ge j 32 with hj | hj
    · have := hole_cols_0
      rw [all_range'_iff] at this
      exact this j (by omega) (by omega)
    · have := hole_cols_1
      rw [all_range'_iff] at this
      exact this j (by omega) (by omega)
  rw [Vec.toFock_eq_of_trie_eq numbering (by simpa only [holeCheck, beq_iff_eq] using hc),
    toFock_combo_basis (by norm_num) basisVec B64 B64_eq _ (keys_hole j)]

/-- The parity on the sixty-four products. -/
theorem parity_lc (a : Fin 64 → ℂ) :
    parityX *ᵥ Φ64 a = Φ64 (colMat 6 64 parityCols *ᵥ a) :=
  diag_lc (d := 6) (by norm_num) (by norm_num) _ parityF parityF_spec parityCols basisVec B64
    B64_eq keys_parity (fun j => by
      have := parity_cols
      rw [all_range_iff] at this
      exact this j j.2) a

theorem hole_omega1_comm :
    colMat 6 64 omega1Cols * colMat 6 64 holeCols = colMat 6 64 holeCols * colMat 6 64 omega1Cols :=
  colMat_mul_eq_of_check (by norm_num) _ _ _ _ keys_hole omega1_keys (by decide +kernel)

theorem parity_omega1_comm :
    colMat 6 64 omega1Cols * colMat 6 64 parityCols =
      colMat 6 64 parityCols * colMat 6 64 omega1Cols :=
  colMat_mul_eq_of_check (by norm_num) _ _ _ _ keys_parity omega1_keys (by decide +kernel)

/-- `𝒮 P = -P 𝒮` on the products. -/
theorem hole_parity_anti :
    colMat 6 64 holeCols * colMat 6 64 parityCols =
      ((-1 : ℤ) : ℂ) • (colMat 6 64 parityCols * colMat 6 64 holeCols) :=
  colMat_mul_eq_smul_of_check (by norm_num) _ _ _ _ _ keys_parity keys_hole (by decide +kernel)

/-! ### On the zero-flux sector of Model I -/

theorem mem_cube_iff (v : Finset EM → ℂ) :
    v ∈ zeroFluxValues cubeTriplet bookOrd ↔ ∃ a, Φ64 a = v := by
  rw [zeroFluxValues_cube, LinearMap.mem_range]

theorem tally1_Φ64 (a : Fin 64 → ℂ) :
    tally bookOrd 1 *ᵥ Φ64 a = (1 / 3 : ℂ) • Φ64 (colMat 6 64 omega1Cols *ᵥ a) := by
  rw [← omega1_lc, Matrix.smul_mulVec, smul_smul]
  norm_num

theorem hole_keeps (v : Finset EM → ℂ) (hv : v ∈ zeroFluxValues cubeTriplet bookOrd) :
    holeMap bookOrd *ᵥ v ∈ zeroFluxValues cubeTriplet bookOrd := by
  obtain ⟨a, rfl⟩ := (mem_cube_iff v).mp hv
  exact (mem_cube_iff _).mpr ⟨_, (hole_lc a).symm⟩

theorem hole_tally_comm (v : Finset EM → ℂ) (hv : v ∈ zeroFluxValues cubeTriplet bookOrd) :
    tally bookOrd 1 *ᵥ (holeMap bookOrd *ᵥ v) = holeMap bookOrd *ᵥ (tally bookOrd 1 *ᵥ v) := by
  obtain ⟨a, rfl⟩ := (mem_cube_iff v).mp hv
  rw [hole_lc, tally1_Φ64, tally1_Φ64, Matrix.mulVec_smul, hole_lc, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hole_omega1_comm]

theorem parity_tally_comm (v : Finset EM → ℂ) (hv : v ∈ zeroFluxValues cubeTriplet bookOrd) :
    tally bookOrd 1 *ᵥ (parityX *ᵥ v) = parityX *ᵥ (tally bookOrd 1 *ᵥ v) := by
  obtain ⟨a, rfl⟩ := (mem_cube_iff v).mp hv
  rw [parity_lc, tally1_Φ64, tally1_Φ64, Matrix.mulVec_smul, parity_lc, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, parity_omega1_comm]

theorem hole_parity_anticomm (v : Finset EM → ℂ)
    (hv : v ∈ zeroFluxValues cubeTriplet bookOrd) :
    holeMap bookOrd *ᵥ (parityX *ᵥ v) = -(parityX *ᵥ (holeMap bookOrd *ᵥ v)) := by
  obtain ⟨a, rfl⟩ := (mem_cube_iff v).mp hv
  rw [parity_lc, hole_lc, hole_lc, parity_lc, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hole_parity_anti, Matrix.smul_mulVec, map_smul]
  simp

/-! ### Without the pair hop -/

theorem tally0_act (v : Vec) :
    (3 : ℂ) • (tally bookOrd 0 *ᵥ Vec.toFock code v) =
      Vec.toFock code (OpC.act parB tally0C v) := by
  rw [← Matrix.smul_mulVec, ← tally3Op_zero, Op.toMat_mulVec_compile numbering parB parB_spec]
  rfl

/-- The list of `𝒮 v`. -/
def holeVec (v : Vec) : Vec := (OpC.act parB holeC v).map fun p => (p.1, upSignF p.1 * p.2)

theorem holeMap_toFock' (v : Vec) :
    holeMap bookOrd *ᵥ Vec.toFock code v = Vec.toFock code (holeVec v) :=
  holeMap_toFock v

theorem hole_tally0_witness :
    Vec.sumAt 12 1366 (OpC.act parB tally0C (holeVec (basisVec 1))) = -6 ∧
      Vec.sumAt 12 1366 (holeVec (OpC.act parB tally0C (basisVec 1))) = 0 := by
  decide +kernel

/-- Without the pair hop, `𝒮` does not commute with the tally on the pair at `y`. -/
theorem hole_tally0_ne :
    tally bookOrd 0 *ᵥ (holeMap bookOrd *ᵥ pairY) ≠
      holeMap bookOrd *ᵥ (tally bookOrd 0 *ᵥ pairY) := by
  intro h
  have e1 : (3 : ℂ) • (tally bookOrd 0 *ᵥ (holeMap bookOrd *ᵥ pairY)) =
      Vec.toFock code (OpC.act parB tally0C (holeVec (basisVec 1))) := by
    rw [pairY_eq, holeMap_toFock', tally0_act]
  have e2 : (3 : ℂ) • (holeMap bookOrd *ᵥ (tally bookOrd 0 *ᵥ pairY)) =
      Vec.toFock code (holeVec (OpC.act parB tally0C (basisVec 1))) := by
    rw [← Matrix.mulVec_smul, pairY_eq, tally0_act, holeMap_toFock']
  rw [h, e2] at e1
  have h4 := congrFun e1 (decode code 1366)
  rw [Vec.toFock_apply numbering _ (by norm_num), Vec.toFock_apply numbering _ (by norm_num),
    hole_tally0_witness.1, hole_tally0_witness.2] at h4
  norm_num at h4

end ModelsCheck

end Artform
