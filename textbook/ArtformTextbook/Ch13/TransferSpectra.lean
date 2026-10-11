import ArtformTextbook.Ch13.TransferCheck
import ArtformTextbook.Ch13.TransferMoments
import ArtformTextbook.Ch12.Models

/-!
# The values of the transfer on the zero-flux sectors

The table of Figure `fig:ml-transfer-spectra`. In the book's order of the modes the zero-flux
values of the real triplets are the span of the sixty-four products, of the complex ones that of
the thirty-six; on them the number of quarks `N` and `6 L` (real) or `(6 L)²` (complex) are the
matrices of the certificate, with common eigenvectors (`TransferSpectra.jointR`,
`TransferSpectra.jointC`). At `N = 6` the complex `L` has the values `±12√2`, found from `(6 L)²`
and two explicit eigenvectors. The table holds in every order of the modes
(`TransferSpectra.Table.map`).
-/

namespace Artform

open scoped Matrix

open Module FockCalc ModelsData SpecCert ModelsCheck Edge TransferCalc TransferData
  TransferCheck

namespace TransferSpectra

/-! ### The number of quarks -/

/-- The number of quarks as a diagonal operator on the tables. -/
noncomputable def numberOp : Matrix (Finset EM) (Finset EM) ℂ :=
  Matrix.diagonal fun n => (n.card : ℂ)

theorem numberSector_eq (N : ℕ) :
    Fock.numberSector EM N = Module.End.eigenspace (Matrix.toLin' numberOp) (N : ℂ) := by
  ext v
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  constructor
  · intro h
    funext n
    rw [numberOp, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hv : v n = 0
    · rw [hv, mul_zero, mul_zero]
    · rw [h n hv]
  · intro h n hn
    have := congrFun h n
    rw [numberOp, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    exact_mod_cast mul_right_cancel₀ hn this

theorem numF_spec (k : ℕ) :
    (fun n : Finset EM => (n.card : ℂ)) (decode code k) = (numF k : ℂ) := by
  simp [numF]

theorem number_lc64 (a : Fin 64 → ℂ) :
    numberOp *ᵥ Φ64 a = Φ64 (colMat 6 64 numCols64 *ᵥ a) :=
  diag_lc (d := 6) (by norm_num) (by norm_num) _ numF numF_spec numCols64 basisVec B64 B64_eq
    keysN64 (fun j => by
      have := numR_cols
      rw [all_range_iff] at this
      exact this j j.2) a

theorem number_lc36 (a : Fin 36 → ℂ) :
    numberOp *ᵥ Φ36 a = Φ36 (colMat 6 36 numCols36 *ᵥ a) :=
  diag_lc (d := 6) (by norm_num) (by norm_num) _ numF numF_spec numCols36 basisVec36 B36 B36_eq
    keysN36 (fun j => by
      have := numC_cols
      rw [all_range_iff] at this
      exact this j j.2) a

/-! ### `6 L` on the products -/

theorem transferR_lc (a : Fin 64 → ℂ) :
    ((6 : ℂ) • transferWords bookOrd true) *ᵥ Φ64 a = Φ64 (colMat 6 64 transferRCols *ᵥ a) := by
  refine mulVec_linearCombination (d := 6) (by norm_num) (by norm_num) _ B64 transferRCols keysR
    (fun j => ?_) a
  rw [B64_eq, ← transfer6_toFock, Vec.toFock_eq_of_trie_eq numbering
    (by simpa only [colCheckT, beq_iff_eq] using transferR_cols j j.2),
    toFock_combo_basis (by norm_num) basisVec B64 B64_eq _ (keysR j)]

theorem transferC_lc (a : Fin 36 → ℂ) :
    ((6 : ℂ) • transferWords bookOrd false) *ᵥ Φ36 a = Φ36 (colMat 6 36 transferCCols *ᵥ a) := by
  refine mulVec_linearCombination (d := 6) (by norm_num) (by norm_num) _ B36 transferCCols keysC
    (fun j => ?_) a
  rw [B36_eq, ← transfer6_toFock, Vec.toFock_eq_of_trie_eq numbering
    (by simpa only [colCheckT, beq_iff_eq] using transferC_cols j j.2),
    toFock_combo_basis (by norm_num) basisVec36 B36 B36_eq _ (keysC j)]

/-- A product of matrices given by columns is a matrix given by columns, checked column by
column. -/
theorem colMat_mul_eq_colMat {d n : ℕ} (hn : n ≤ 2 ^ d) (A B C : List Vec)
    (hB : ∀ j : Fin n, keysLt n (B.getD j []) = true)
    (h : ∀ j : Fin n, Vec.trie d (apply A (B.getD j [])) = Vec.trie d (C.getD j [])) :
    colMat d n A * colMat d n B = colMat d n C := by
  ext i j
  have hcol : (colMat d n A * colMat d n B) i j = vecFun d n (apply A (B.getD j [])) i := by
    rw [← colMat_mulVec hn A _ (hB j)]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, vecFun, colMat, Matrix.of_apply]
  rw [hcol, vecFun_eq_of_trie_eq (h j)]
  rfl

theorem transferC2_lc (a : Fin 36 → ℂ) :
    (((6 : ℂ) • transferWords bookOrd false) * ((6 : ℂ) • transferWords bookOrd false)) *ᵥ
      Φ36 a = Φ36 (colMat 6 36 transferC2Cols *ᵥ a) := by
  rw [← Matrix.mulVec_mulVec, transferC_lc, transferC_lc, Matrix.mulVec_mulVec,
    colMat_mul_eq_colMat (by norm_num) _ _ _ keysC transferC2_cols]

/-! ### Joint multiplicities -/

/-- The values of the real certificate. -/
def nuR (r : ℕ) (k : Fin 64) : ℤ := ((eigR r).getD k (0, [])).1

/-- The values of the complex certificate. -/
def nuC (r : ℕ) (k : Fin 36) : ℤ := ((eigC r).getD k (0, [])).1

theorem eigR_snd (r : ℕ) : (eigR r).map Prod.snd = transferREig.map Prod.snd := by
  simp only [eigR, List.map_map]
  rfl

theorem eigC_snd (r : ℕ) : (eigC r).map Prod.snd = transferCEig.map Prod.snd := by
  simp only [eigC, List.map_map]
  rfl

theorem diagR (r : ℕ) (cols : List Vec) (h : eigOK 6 64 cols (eigR r) = true) :
    colMat 6 64 cols * Cmat 6 64 (transferREig.map Prod.snd) =
      Cmat 6 64 (transferREig.map Prod.snd) * Matrix.diagonal fun k => (nuR r k : ℂ) := by
  rw [← eigR_snd r]
  exact colMat_mul_Cmat (by norm_num) cols _ h

theorem diagC (r : ℕ) (cols : List Vec) (h : eigOK 6 36 cols (eigC r) = true) :
    colMat 6 36 cols * Cmat 6 36 (transferCEig.map Prod.snd) =
      Cmat 6 36 (transferCEig.map Prod.snd) * Matrix.diagonal fun k => (nuC r k : ℂ) := by
  rw [← eigC_snd r]
  exact colMat_mul_Cmat (by norm_num) cols _ h

theorem invR :
    colMat 6 64 transferRD * Cmat 6 64 (transferREig.map Prod.snd) =
      Matrix.diagonal (fun k : Fin 64 => (transferRDg.getD k 0 : ℂ)) ∧
        ∀ k : Fin 64, (transferRDg.getD k 0 : ℂ) ≠ 0 := by
  rw [← eigR_snd 0]
  exact D_mul_Cmat (by norm_num) _ _ _ _ transferR_eig0 transferR_inv0

theorem invC :
    colMat 6 36 transferCD * Cmat 6 36 (transferCEig.map Prod.snd) =
      Matrix.diagonal (fun k : Fin 36 => (transferCDg.getD k 0 : ℂ)) ∧
        ∀ k : Fin 36, (transferCDg.getD k 0 : ℂ) ≠ 0 := by
  rw [← eigC_snd 0]
  exact D_mul_Cmat (by norm_num) _ _ _ _ transferC_eig0 transferC_inv0

theorem jointR (N μ : ℂ) :
    finrank ℂ ↥(LinearMap.range Φ64 ⊓ Module.End.eigenspace (Matrix.toLin' numberOp) N ⊓
      Module.End.eigenspace (Matrix.toLin' ((6 : ℂ) • transferWords bookOrd true)) μ) =
      (Finset.univ.filter fun k => (nuR 0 k : ℂ) = N ∧ (nuR 1 k : ℂ) = μ).card := by
  rw [finrank_inf_inf_eigenspace _ _ _ Φ64 Φ64_injective rfl _ _
    (fun a => by rw [Matrix.toLin'_apply, number_lc64])
    (fun a => by rw [Matrix.toLin'_apply, transferR_lc]),
    finrank_inf_eigenspace_of_diag _ _ _ _ _ _ _ (diagR 0 _ transferR_eig0)
      (diagR 1 _ transferR_eig1) invR.1 invR.2]

theorem singleR (N : ℂ) :
    finrank ℂ ↥(LinearMap.range Φ64 ⊓ Module.End.eigenspace (Matrix.toLin' numberOp) N) =
      (Finset.univ.filter fun k => (nuR 0 k : ℂ) = N).card := by
  rw [finrank_inf_eigenspace _ _ Φ64 Φ64_injective rfl _
    (fun a => by rw [Matrix.toLin'_apply, number_lc64]),
    finrank_eigenspace_colMat (by norm_num) numCols64 transferRD (eigR 0) transferRDg
      transferR_eig0 transferR_inv0]
  rfl

theorem jointC (N μ : ℂ) :
    finrank ℂ ↥(LinearMap.range Φ36 ⊓ Module.End.eigenspace (Matrix.toLin' numberOp) N ⊓
      Module.End.eigenspace (Matrix.toLin' (((6 : ℂ) • transferWords bookOrd false) *
        ((6 : ℂ) • transferWords bookOrd false))) μ) =
      (Finset.univ.filter fun k => (nuC 0 k : ℂ) = N ∧ (nuC 1 k : ℂ) = μ).card := by
  rw [finrank_inf_inf_eigenspace _ _ _ Φ36 Φ36_injective rfl _ _
    (fun a => by rw [Matrix.toLin'_apply, number_lc36])
    (fun a => by rw [Matrix.toLin'_apply, transferC2_lc]),
    finrank_inf_eigenspace_of_diag _ _ _ _ _ _ _ (diagC 0 _ transferC_eig0)
      (diagC 1 _ transferC_eig1) invC.1 invC.2]

theorem singleC (N : ℂ) :
    finrank ℂ ↥(LinearMap.range Φ36 ⊓ Module.End.eigenspace (Matrix.toLin' numberOp) N) =
      (Finset.univ.filter fun k => (nuC 0 k : ℂ) = N).card := by
  rw [finrank_inf_eigenspace _ _ Φ36 Φ36_injective rfl _
    (fun a => by rw [Matrix.toLin'_apply, number_lc36]),
    finrank_eigenspace_colMat (by norm_num) numCols36 transferCD (eigC 0) transferCDg
      transferC_eig0 transferC_inv0]
  rfl

/-! ### Counting -/

theorem card_filter2 {n : ℕ} (ν₀ ν₁ : Fin n → ℤ) (N : ℕ) {w : ℤ} {c : ℂ} (h : c = w) :
    (Finset.univ.filter fun k => (ν₀ k : ℂ) = (N : ℂ) ∧ (ν₁ k : ℂ) = c).card =
      (Finset.univ.filter fun k => ν₀ k = N ∧ ν₁ k = w).card := by
  subst h
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1]; push_cast; rfl, by rw [h2]⟩

theorem card_filter2_zero {n : ℕ} (ν₀ ν₁ : Fin n → ℤ) (N : ℕ) {c : ℂ}
    (h : ∀ k, ν₀ k = N → (ν₁ k : ℂ) ≠ c) :
    (Finset.univ.filter fun k => (ν₀ k : ℂ) = (N : ℂ) ∧ (ν₁ k : ℂ) = c).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro k _ ⟨h1, h2⟩
  exact h k (by exact_mod_cast h1) h2

theorem card_filter1 {n : ℕ} (ν₀ : Fin n → ℤ) (N : ℕ) :
    (Finset.univ.filter fun k => (ν₀ k : ℂ) = (N : ℂ)).card =
      (Finset.univ.filter fun k => ν₀ k = N).card := by
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h1
    exact_mod_cast h1
  · intro h1
    rw [h1]
    push_cast
    rfl

theorem countR : (∀ N ∈ [3, 5, 7, 9],
    (Finset.univ.filter fun k => nuR 0 k = N ∧ nuR 1 k = 36).card = 4 ∧
    (Finset.univ.filter fun k => nuR 0 k = N ∧ nuR 1 k = -36).card = 4) ∧
    (∀ k, nuR 0 k ∈ [3, 5, 7, 9] → nuR 1 k = 36 ∨ nuR 1 k = -36) ∧
    (Finset.univ.filter fun k => nuR 0 k = 6 ∧ nuR 1 k = 144).card = 1 ∧
    (Finset.univ.filter fun k => nuR 0 k = 6 ∧ nuR 1 k = -144).card = 1 ∧
    (Finset.univ.filter fun k => nuR 0 k = 6 ∧ nuR 1 k = 0).card = 18 ∧
    (∀ k, nuR 0 k = 6 → nuR 1 k = 144 ∨ nuR 1 k = -144 ∨ nuR 1 k = 0) ∧
    ∀ k, nuR 0 k ∉ [3, 5, 6, 7, 9] → nuR 1 k = 0 := by
  decide +kernel

theorem secR (N : ℕ) (μ : ℂ) :
    finrank ℂ ↥(LinearMap.range Φ64 ⊓ Fock.numberSector EM N ⊓
      Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd true)) μ) =
      (Finset.univ.filter fun k => (nuR 0 k : ℂ) = N ∧ (nuR 1 k : ℂ) = 6 * μ).card := by
  rw [numberSector_eq, ← toLin'_smul_eigenspace _ (by norm_num : (6 : ℂ) ≠ 0) μ, jointR]

theorem secR_card (N : ℕ) :
    finrank ℂ ↥(LinearMap.range Φ64 ⊓ Fock.numberSector EM N) =
      (Finset.univ.filter fun k => (nuR 0 k : ℂ) = N).card := by
  rw [numberSector_eq, singleR]

open Classical in
/-- The table of Figure `fig:ml-transfer-spectra` on a sector `Z` with the operator `L` (the body of
the statement's `table`). -/
def Table (Z : Submodule ℂ (Finset EM → ℂ)) (L : Module.End ℂ (Finset EM → ℂ)) (real : Bool) :
    Prop :=
  let sec : ℕ → Submodule ℂ (Finset EM → ℂ) := fun N => Z ⊓ Fock.numberSector EM N
  (∀ N ∈ ({3, 9} : Set ℕ), ∀ μ : ℂ,
    finrank ℂ ↥(sec N ⊓ Module.End.eigenspace L μ) = if μ = 6 ∨ μ = -6 then 4 else 0) ∧
  (∀ N ∈ ({5, 7} : Set ℕ), if real then ∀ μ : ℂ,
    finrank ℂ ↥(sec N ⊓ Module.End.eigenspace L μ) = if μ = 6 ∨ μ = -6 then 4 else 0
    else sec N = ⊥) ∧
  (∀ μ : ℂ, finrank ℂ ↥(sec 6 ⊓ Module.End.eigenspace L μ) =
    if real then (if μ = 24 ∨ μ = -24 then 1 else if μ = 0 then 18 else 0)
    else (if μ = ((12 * Real.sqrt 2 : ℝ) : ℂ) ∨ μ = -((12 * Real.sqrt 2 : ℝ) : ℂ) then 1
      else if μ = 0 then 16 else 0)) ∧
  ∀ N, N ∉ ({3, 5, 6, 7, 9} : Set ℕ) → ∀ v ∈ sec N, L v = 0

open Classical in
theorem tableR_pm6 (N : ℕ) (hN : N ∈ [3, 5, 7, 9]) (μ : ℂ) :
    finrank ℂ ↥(LinearMap.range Φ64 ⊓ Fock.numberSector EM N ⊓
      Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd true)) μ) =
      if μ = 6 ∨ μ = -6 then 4 else 0 := by
  rw [secR]
  obtain ⟨h1, h2, -⟩ := countR
  have hNz : ((N : ℕ) : ℤ) ∈ [3, 5, 7, 9] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hN ⊢
    omega
  by_cases h6 : μ = 6
  · rw [ite_eq_left (Or.inl h6), card_filter2 _ _ N (w := 36) (by rw [h6]; norm_num)]
    exact ((h1 _ hNz).1)
  by_cases hm6 : μ = -6
  · rw [ite_eq_left (Or.inr hm6), card_filter2 _ _ N (w := -36) (by rw [hm6]; norm_num)]
    exact ((h1 _ hNz).2)
  rw [ite_eq_right (by tauto)]
  refine card_filter2_zero _ _ N fun k hk hc => ?_
  rcases h2 k (hk ▸ hNz) with h' | h' <;> rw [h'] at hc <;> push_cast at hc
  · exact h6 (by linear_combination -hc / 6)
  · exact hm6 (by linear_combination -hc / 6)

open Classical in
theorem tableR : Table (LinearMap.range Φ64) (Matrix.toLin' (transferWords bookOrd true)) true := by
  obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := countR
  refine ⟨fun N hN μ => tableR_pm6 N ?_ μ, fun N hN => ?_, fun μ => ?_, fun N hN v hv => ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl <;> simp
  · simp only [ite_true]
    refine fun μ => tableR_pm6 N ?_ μ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl <;> simp
  · simp only [ite_true]
    rw [secR]
    by_cases hp : μ = 24
    · rw [ite_eq_left (Or.inl hp), card_filter2 _ _ 6 (w := 144) (by rw [hp]; norm_num)]
      exact_mod_cast h3
    by_cases hm : μ = -24
    · rw [ite_eq_left (Or.inr hm), card_filter2 _ _ 6 (w := -144) (by rw [hm]; norm_num)]
      exact_mod_cast h4
    rw [ite_eq_right (by tauto)]
    by_cases h0 : μ = 0
    · rw [ite_eq_left h0, card_filter2 _ _ 6 (w := 0) (by rw [h0]; norm_num)]
      exact_mod_cast h5
    rw [ite_eq_right h0]
    refine card_filter2_zero _ _ 6 fun k hk h => ?_
    rcases h6 k (by exact_mod_cast hk) with h' | h' | h' <;> rw [h'] at h <;> push_cast at h
    · exact hp (by linear_combination -h / 6)
    · exact hm (by linear_combination -h / 6)
    · exact h0 (by linear_combination -h / 6)
  · -- `L = 0` on the other sectors
    have hle : LinearMap.range Φ64 ⊓ Fock.numberSector EM N ≤
        Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd true)) 0 := by
      have heq := Submodule.eq_of_le_of_finrank_eq
        (inf_le_left : LinearMap.range Φ64 ⊓ Fock.numberSector EM N ⊓
          Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd true)) 0 ≤ _) (by
          rw [secR, secR_card, mul_zero]
          congr 1
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Int.cast_eq_zero,
            and_iff_left_iff_imp]
          intro hk
          refine h7 k fun hmem => hN ?_
          have hk' : nuR 0 k = N := by exact_mod_cast hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          omega)
      rw [← heq]
      exact inf_le_right
    have := hle hv
    rw [Module.End.mem_eigenspace_iff, zero_smul] at this
    exact this

/-! ### The complex triplets -/

theorem countC : (Finset.univ.filter fun k => nuC 0 k = 3).card = 8 ∧
    (Finset.univ.filter fun k => nuC 0 k = 9).card = 8 ∧
    (Finset.univ.filter fun k => nuC 0 k = 5).card = 0 ∧
    (Finset.univ.filter fun k => nuC 0 k = 7).card = 0 ∧
    (Finset.univ.filter fun k => nuC 0 k = 6 ∧ nuC 1 k = 0).card = 16 ∧
    (Finset.univ.filter fun k => nuC 0 k = 6 ∧ nuC 1 k = 10368).card = 2 ∧
    (∀ k, nuC 0 k = 6 → nuC 1 k = 0 ∨ nuC 1 k = 10368) ∧
    (∀ k, nuC 0 k ∉ [0, 3, 6, 9, 12] → False) ∧
    (∀ k, nuC 0 k = 0 ∨ nuC 0 k = 12 → nuC 1 k = 0) := by
  decide +kernel

theorem countR_3_9 : (Finset.univ.filter fun k => nuR 0 k = 3).card = 8 ∧
    (Finset.univ.filter fun k => nuR 0 k = 9).card = 8 := by
  decide +kernel

/-- The vectors of the complex certificate with `(6 L)² = 0` are killed by `6 L`. -/
theorem transferC_null0 : transferCEig.all (fun e => e.1.getD 1 0 != 0 ||
    Vec.trie 6 (apply transferCCols e.2) == Vec.trie 6 []) = true := by
  decide +kernel

/-- The sectors with three and with nine quarks: both `6 L` act alike on their products. -/
theorem sector39_agree : [2, 3, 4, 5, 16, 24, 32, 40, 23, 31, 39, 47, 58, 59, 60, 61].all
    (fun j => Vec.trie 12 (transfer6 true (basisVec j)) ==
      Vec.trie 12 (transfer6 false (basisVec j))) = true := by
  set_option maxRecDepth 100000 in decide +kernel

set_option maxRecDepth 100000 in
/-- `L` on the full vertices, complex triplet: `6 L |full⟩ = -12 (6 ψ₀)` at each end. -/
theorem full_transfer :
    (Vec.trie 12 (transfer6 false (basisVec 56)) == Vec.trie 12 (Vec.smul (-12) singletVec)) =
      true ∧
    (Vec.trie 12 (transfer6 false (basisVec 7)) == Vec.trie 12 (Vec.smul (-12) singletVec)) =
      true := by
  decide +kernel

/-- The subspace on which every certificate vector with the given values is killed by an
operator lies in its kernel. -/
theorem inf_le_ker {n d : ℕ} (hn : n ≤ 2 ^ d) (Φ : (Fin n → ℂ) →ₗ[ℂ] (Finset EM → ℂ))
    (hΦ : Function.Injective Φ) (T₁ T₂ T₃ : Module.End ℂ (Finset EM → ℂ))
    (K₁ K₂ : Matrix (Fin n) (Fin n) ℂ) (cols₃ : List Vec) (vs : List Vec)
    (hT₁ : ∀ a, T₁ (Φ a) = Φ (K₁ *ᵥ a)) (hT₂ : ∀ a, T₂ (Φ a) = Φ (K₂ *ᵥ a))
    (hT₃ : ∀ a, T₃ (Φ a) = Φ (colMat d n cols₃ *ᵥ a))
    (D : Matrix (Fin n) (Fin n) ℂ) (ν₁ ν₂ dg : Fin n → ℂ)
    (h₁ : K₁ * Cmat d n vs = Cmat d n vs * Matrix.diagonal ν₁)
    (h₂ : K₂ * Cmat d n vs = Cmat d n vs * Matrix.diagonal ν₂)
    (hDC : D * Cmat d n vs = Matrix.diagonal dg) (hdg : ∀ k, dg k ≠ 0) (μ₁ μ₂ : ℂ)
    (hkeys : ∀ k : Fin n, keysLt n (vs.getD k []) = true)
    (hnull : ∀ k : Fin n, ν₁ k = μ₁ → ν₂ k = μ₂ →
      Vec.trie d (apply cols₃ (vs.getD k [])) = Vec.trie d []) :
    LinearMap.range Φ ⊓ Module.End.eigenspace T₁ μ₁ ⊓ Module.End.eigenspace T₂ μ₂ ≤
      Module.End.eigenspace T₃ 0 := by
  intro v hv
  obtain ⟨⟨⟨a, rfl⟩, hv₁⟩, hv₂⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, hT₁, ← map_smul] at hv₁
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, hT₂, ← map_smul] at hv₂
  have ha₁ : a ∈ Module.End.eigenspace (Matrix.toLin' K₁) μ₁ := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hΦ hv₁
  have ha₂ : a ∈ Module.End.eigenspace (Matrix.toLin' K₂) μ₂ := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hΦ hv₂
  obtain ⟨b, rfl, hb⟩ := (mem_eigenspace_iff_of_diag K₁ _ D ν₁ dg h₁ hDC hdg μ₁ a).mp ha₁
  obtain ⟨b', hbb', hb'⟩ := (mem_eigenspace_iff_of_diag K₂ _ D ν₂ dg h₂ hDC hdg μ₂ _).mp ha₂
  have hinj : Function.Injective (Matrix.toLin' (Cmat d n vs)) := by
    intro x y hxy
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hxy
    have h := congrArg (fun z => D *ᵥ z) hxy
    simp only [Matrix.mulVec_mulVec, hDC] at h
    funext k
    have hk := congrFun h k
    rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal] at hk
    exact mul_left_cancel₀ (hdg k) hk
  have hbb : b = b' := hinj (by rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact hbb')
  subst hbb
  rw [Module.End.mem_eigenspace_iff, hT₃, zero_smul]
  have hcol : colMat d n cols₃ *ᵥ (Cmat d n vs *ᵥ b) = 0 := by
    rw [Matrix.mulVec_mulVec]
    funext i
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : ν₁ k = μ₁ ∧ ν₂ k = μ₂
    · have h0 := congrFun (Cmat_col (d := d) vs (colMat d n cols₃) k) i
      simp only [Matrix.col_apply] at h0
      rw [h0, colMat_mulVec hn _ _ (hkeys k), vecFun_eq_of_trie_eq (hnull k hk.1 hk.2)]
      simp [vecFun, Vec.sumAt]
    · have : b k = 0 := by
        by_cases h1 : ν₁ k = μ₁
        · exact hb' k fun h2 => hk ⟨h1, h2⟩
        · exact hb k h1
      rw [this, mul_zero]
  rw [hcol, map_zero]

theorem endSector_le_numberSector (a b : ℕ) :
    endSector (Fin 3) (Fin 2) a b ≤ Fock.numberSector EM (a + b) := fun v hv n hn => by
  obtain ⟨h1, h2⟩ := hv n hn
  rw [← Finset.card_toLeft_add_card_toRight, h1, h2]

theorem secC_card (N : ℕ) :
    finrank ℂ ↥(LinearMap.range Φ36 ⊓ Fock.numberSector EM N) =
      (Finset.univ.filter fun k => nuC 0 k = N).card := by
  rw [numberSector_eq, singleC, card_filter1]

theorem secR_card' (N : ℕ) :
    finrank ℂ ↥(LinearMap.range Φ64 ⊓ Fock.numberSector EM N) =
      (Finset.univ.filter fun k => nuR 0 k = N).card := by
  rw [secR_card, card_filter1]

/-! ### The named states for the complex triplets -/

theorem fullX_eq_B36 : fullX = B36 30 := rfl

theorem fullY_eq_B36 : fullY = B36 5 := rfl

theorem fullX_eq : fullX = Vec.toFock code (basisVec 56) := B64_lit.2.2.2.2.2.2.2.2.2

theorem fullY_eq : fullY = Vec.toFock code (basisVec 7) := B64_lit.2.2.1

theorem B36_mem_range (j : Fin 36) : B36 j ∈ LinearMap.range Φ36 := by
  rw [Φ36, Fintype.range_linearCombination]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem transferC_singlet :
    transferWords bookOrd false *ᵥ singlet = (-12 : ℂ) • (fullX + fullY) := by
  have h := transfer_check false singletVec _ singlet_transfer.1
  rw [Vec.toFock_combo] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [singlet_eq, Matrix.mulVec_smul, fullX_eq, fullY_eq]
  apply smul_right_injective _ (by norm_num : (6 : ℂ) ≠ 0)
  simp only
  rw [smul_comm, h]
  push_cast
  module

theorem transferC_full :
    transferWords bookOrd false *ᵥ fullX = (-12 : ℂ) • singlet ∧
      transferWords bookOrd false *ᵥ fullY = (-12 : ℂ) • singlet := by
  have h1 := transfer_check false _ _ full_transfer.1
  have h2 := transfer_check false _ _ full_transfer.2
  rw [Vec.toFock_smul] at h1 h2
  constructor
  · apply smul_right_injective _ (by norm_num : (6 : ℂ) ≠ 0)
    simp only
    rw [fullX_eq, h1, singlet_eq]
    simp only [smul_smul]
    norm_num
  · apply smul_right_injective _ (by norm_num : (6 : ℂ) ≠ 0)
    simp only
    rw [fullY_eq, h2, singlet_eq]
    simp only [smul_smul]
    norm_num

/-- The two eigenvectors `ψ₀ ∓ (√2/2) (|full_x⟩ + |full_y⟩)` with the values `±12√2`. -/
theorem sqrt_two_eigen (sgn : ℂ) (hs : sgn = 1 ∨ sgn = -1) :
    transferWords bookOrd false *ᵥ
        (singlet - (sgn * ((Real.sqrt 2 : ℝ) : ℂ) / 2) • (fullX + fullY)) =
      (sgn * ((12 * Real.sqrt 2 : ℝ) : ℂ)) •
        (singlet - (sgn * ((Real.sqrt 2 : ℝ) : ℂ) / 2) • (fullX + fullY)) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hsg : sgn * sgn = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_add, transferC_singlet,
    transferC_full.1, transferC_full.2]
  push_cast
  simp only [smul_sub, smul_add, smul_smul]
  have c1 : sgn * (12 * ((Real.sqrt 2 : ℝ) : ℂ)) * (sgn * ((Real.sqrt 2 : ℝ) : ℂ) / 2) = 12 := by
    linear_combination (6 * sgn * sgn) * h2 + 12 * hsg
  rw [c1]
  module

theorem sqrt_two_eigen_ne (sgn : ℂ) :
    singlet - (sgn * ((Real.sqrt 2 : ℝ) : ℂ) / 2) • (fullX + fullY) ≠ 0 := by
  intro h
  have h1 := congrFun h (decode code 2709)
  have hx : fullX (decode code 2709) = 0 := by
    rw [fullX_eq, Vec.toFock_apply numbering _ (by norm_num)]
    norm_cast
  have hy : fullY (decode code 2709) = 0 := by
    rw [fullY_eq, Vec.toFock_apply numbering _ (by norm_num)]
    norm_cast
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, hx, hy, add_zero, smul_zero, sub_zero,
    singlet_at.1, Pi.zero_apply] at h1
  norm_num at h1

/-! ### The complex table -/

theorem keysC_eig : ∀ k : Fin 36, keysLt 36 ((transferCEig.map Prod.snd).getD k []) = true := by
  decide +kernel

theorem nullC : ∀ k : Fin 36, nuC 1 k = 0 →
    Vec.trie 6 (apply transferCCols ((transferCEig.map Prod.snd).getD k [])) = Vec.trie 6 [] := by
  decide +kernel

/-- `L` and `L²` on the six-quark sector of the complex triplets. -/
theorem secC_sq (lam : ℂ) :
    finrank ℂ ↥(LinearMap.range Φ36 ⊓ Fock.numberSector EM 6 ⊓
      Module.End.eigenspace (Matrix.toLin' (((6 : ℂ) • transferWords bookOrd false) *
        ((6 : ℂ) • transferWords bookOrd false))) lam) =
      (Finset.univ.filter fun k => (nuC 0 k : ℂ) = ((6 : ℕ) : ℂ) ∧ (nuC 1 k : ℂ) = lam).card := by
  rw [numberSector_eq, jointC]

theorem eig_le_sq (μ : ℂ) :
    Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd false)) μ ≤
      Module.End.eigenspace (Matrix.toLin' (((6 : ℂ) • transferWords bookOrd false) *
        ((6 : ℂ) • transferWords bookOrd false))) (36 * μ ^ 2) := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
  simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, hv, smul_smul]
  congr 1
  ring

theorem secC_ker :
    LinearMap.range Φ36 ⊓ Fock.numberSector EM 6 ⊓
        Module.End.eigenspace (Matrix.toLin' (((6 : ℂ) • transferWords bookOrd false) *
          ((6 : ℂ) • transferWords bookOrd false))) 0 ≤
      Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd false)) 0 := by
  rw [numberSector_eq, ← toLin'_smul_eigenspace (transferWords bookOrd false)
    (by norm_num : (6 : ℂ) ≠ 0) 0, mul_zero]
  refine inf_le_ker (d := 6) (by norm_num) Φ36 Φ36_injective _ _ _ _ _ transferCCols
    (transferCEig.map Prod.snd) (fun a => by rw [Matrix.toLin'_apply, number_lc36])
    (fun a => by rw [Matrix.toLin'_apply, transferC2_lc])
    (fun a => by rw [Matrix.toLin'_apply, transferC_lc]) _ _ _ _
    (diagC 0 _ transferC_eig0) (diagC 1 _ transferC_eig1) invC.1 invC.2 _ _ keysC_eig
    (fun k _ h₂ => nullC k (by exact_mod_cast h₂))

theorem psi_mem (sgn : ℂ) :
    singlet - (sgn * ((Real.sqrt 2 : ℝ) : ℂ) / 2) • (fullX + fullY) ∈
      LinearMap.range Φ36 ⊓ Fock.numberSector EM 6 := by
  have hx : fullX ∈ Fock.numberSector EM 6 := B64_mem_numberSector 56
  have hy : fullY ∈ Fock.numberSector EM 6 := B64_mem_numberSector 7
  have hs : singlet ∈ Fock.numberSector EM 6 :=
    endSector_le_numberSector 3 3 singlet_mem_endSector
  refine ⟨Submodule.sub_mem _ singlet_mem_Φ36 (Submodule.smul_mem _ _
    (Submodule.add_mem _ ?_ ?_)), Submodule.sub_mem _ hs (Submodule.smul_mem _ _
      (Submodule.add_mem _ hx hy))⟩
  · rw [fullX_eq_B36]
    exact B36_mem_range 30
  · rw [fullY_eq_B36]
    exact B36_mem_range 5

/-- The values `±12√2`: each once on the six-quark sector. -/
theorem tableC6_pm (sgn : ℂ) (hs : sgn = 1 ∨ sgn = -1) :
    finrank ℂ ↥(LinearMap.range Φ36 ⊓ Fock.numberSector EM 6 ⊓
      Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd false))
        (sgn * ((12 * Real.sqrt 2 : ℝ) : ℂ))) = 1 := by
  set S := LinearMap.range Φ36 ⊓ Fock.numberSector EM 6
  set E : ℂ → Submodule ℂ (Finset EM → ℂ) := fun s => S ⊓
    Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd false))
      (s * ((12 * Real.sqrt 2 : ℝ) : ℂ)) with hE
  have hx2 : (((12 * Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 288 := by
    rw [← Complex.ofReal_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hle : ∀ s : ℂ, s = 1 ∨ s = -1 → E s ≤ S ⊓ Module.End.eigenspace (Matrix.toLin'
      (((6 : ℂ) • transferWords bookOrd false) * ((6 : ℂ) • transferWords bookOrd false)))
        10368 := fun s hs' => by
    have h := inf_le_inf_left S (eig_le_sq (s * ((12 * Real.sqrt 2 : ℝ) : ℂ)))
    have hsq : (36 : ℂ) * (s * ((12 * Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 10368 := by
      rw [mul_pow, hx2]
      rcases hs' with rfl | rfl <;> norm_num
    rwa [hsq] at h
  have hQ : finrank ℂ ↥(S ⊓ Module.End.eigenspace (Matrix.toLin'
      (((6 : ℂ) • transferWords bookOrd false) * ((6 : ℂ) • transferWords bookOrd false)))
        10368) = 2 := by
    rw [secC_sq, card_filter2 _ _ 6 (w := 10368) (by norm_num)]
    exact_mod_cast countC.2.2.2.2.2.1
  have hdisj : E 1 ⊓ E (-1) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at h1 h2
    rw [h1] at h2
    have h3 : (2 * ((12 * Real.sqrt 2 : ℝ) : ℂ)) • v = 0 := by
      have e : (2 * ((12 * Real.sqrt 2 : ℝ) : ℂ)) =
          1 * ((12 * Real.sqrt 2 : ℝ) : ℂ) - -1 * ((12 * Real.sqrt 2 : ℝ) : ℂ) := by ring
      rw [e, sub_smul, h2, sub_self]
    have hne : (2 * ((12 * Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
      refine mul_ne_zero two_ne_zero ?_
      exact_mod_cast (by positivity : (12 * Real.sqrt 2 : ℝ) ≠ 0)
    exact (Submodule.mem_bot ℂ).mpr ((smul_eq_zero.mp h3).resolve_left hne)
  have hpos : ∀ s : ℂ, s = 1 ∨ s = -1 → 1 ≤ finrank ℂ ↥(E s) := fun s hs' => by
    refine Nat.one_le_iff_ne_zero.mpr fun h0 => ?_
    have hbot := Submodule.finrank_eq_zero.mp h0
    have hmem : singlet - (s * ((Real.sqrt 2 : ℝ) : ℂ) / 2) • (fullX + fullY) ∈ E s := by
      refine ⟨psi_mem s, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact sqrt_two_eigen s hs'
    rw [hbot, Submodule.mem_bot] at hmem
    exact sqrt_two_eigen_ne s hmem
  have hsum : finrank ℂ ↥(E 1) + finrank ℂ ↥(E (-1)) ≤ 2 := by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq, hdisj, finrank_bot, add_zero, ← hQ]
    exact Submodule.finrank_mono (sup_le (hle 1 (Or.inl rfl)) (hle (-1) (Or.inr rfl)))
  have h1 := hpos 1 (Or.inl rfl)
  have h2 := hpos (-1) (Or.inr rfl)
  change finrank ℂ ↥(E sgn) = 1
  rcases hs with rfl | rfl <;> omega

/-- The value `0`: sixteen times on the six-quark sector. -/
theorem tableC6_zero :
    finrank ℂ ↥(LinearMap.range Φ36 ⊓ Fock.numberSector EM 6 ⊓
      Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd false)) 0) = 16 := by
  have heq : LinearMap.range Φ36 ⊓ Fock.numberSector EM 6 ⊓
      Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd false)) 0 =
      LinearMap.range Φ36 ⊓ Fock.numberSector EM 6 ⊓
      Module.End.eigenspace (Matrix.toLin' (((6 : ℂ) • transferWords bookOrd false) *
        ((6 : ℂ) • transferWords bookOrd false))) 0 := by
    apply le_antisymm
    · have h := inf_le_inf_left (LinearMap.range Φ36 ⊓ Fock.numberSector EM 6) (eig_le_sq 0)
      rwa [show (36 : ℂ) * 0 ^ 2 = 0 by norm_num] at h
    · exact le_inf inf_le_left secC_ker
  rw [heq, secC_sq, card_filter2 _ _ 6 (w := 0) (by norm_num)]
  exact_mod_cast countC.2.2.2.2.1

/-- No other value on the six-quark sector. -/
theorem tableC6_other (μ : ℂ) (h0 : μ ≠ 0) (hp : μ ≠ ((12 * Real.sqrt 2 : ℝ) : ℂ))
    (hm : μ ≠ -((12 * Real.sqrt 2 : ℝ) : ℂ)) :
    finrank ℂ ↥(LinearMap.range Φ36 ⊓ Fock.numberSector EM 6 ⊓
      Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd false)) μ) = 0 := by
  have hx2 : (((12 * Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 288 := by
    rw [← Complex.ofReal_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h := Submodule.finrank_mono
    (inf_le_inf_left (LinearMap.range Φ36 ⊓ Fock.numberSector EM 6) (eig_le_sq μ))
  rw [secC_sq] at h
  refine Nat.le_zero.mp (h.trans (le_of_eq ?_))
  refine card_filter2_zero _ _ 6 fun k hk hc => ?_
  rcases countC.2.2.2.2.2.2.1 k (by exact_mod_cast hk) with h' | h' <;> rw [h'] at hc <;>
    push_cast at hc
  · exact h0 (pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linear_combination -hc / 36))
  · have : (μ - ((12 * Real.sqrt 2 : ℝ) : ℂ)) * (μ + ((12 * Real.sqrt 2 : ℝ) : ℂ)) = 0 := by
      linear_combination -hc / 36 - hx2
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hp (sub_eq_zero.mp h1)
    · exact hm (eq_neg_of_add_eq_zero_left h1)

/-! ### The sectors with three and with nine quarks -/

/-- The number of quarks of the product `j` of the eight. -/
def nq64 (j : Fin 64) : ℕ := nq (j / 8) + nq (j % 8)

theorem numCols64_getD : ∀ j : Fin 64,
    numCols64.getD j [] = [((j : ℕ), ((nq64 j : ℕ) : ℤ))] := by
  decide +kernel

theorem colMat_num64 :
    colMat 6 64 numCols64 = Matrix.diagonal fun j => ((nq64 j : ℕ) : ℂ) := by
  ext i j
  have h := congrFun (vecFun_single (d := 6) (by norm_num) j ((nq64 j : ℕ) : ℤ)) i
  simp only [vecFun] at h
  rw [colMat, Matrix.of_apply, numCols64_getD, h, Pi.single_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- A combination of products with `N` quarks in all uses only products with `N` quarks. -/
theorem coeff_eq_zero (N : ℕ) (a : Fin 64 → ℂ) (h : Φ64 a ∈ Fock.numberSector EM N)
    (j : Fin 64) (hj : nq64 j ≠ N) : a j = 0 := by
  rw [numberSector_eq, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, number_lc64,
    colMat_num64, ← map_smul] at h
  have h' := congrFun (Φ64_injective h) j
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h'
  exact (mul_eq_mul_right_iff.mp h').resolve_left (by exact_mod_cast hj)

theorem mulVec_Φ64 (X : Matrix (Finset EM) (Finset EM) ℂ) (a : Fin 64 → ℂ) :
    X *ᵥ Φ64 a = ∑ j, a j • (X *ᵥ B64 j) := by
  rw [Φ64, Fintype.linearCombination_apply, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]

theorem sector39_list : ∀ j : Fin 64, nq64 j = 3 ∨ nq64 j = 9 →
    (j : ℕ) ∈ [2, 3, 4, 5, 16, 24, 32, 40, 23, 31, 39, 47, 58, 59, 60, 61] := by
  decide

theorem agree39 (j : Fin 64) (hj : nq64 j = 3 ∨ nq64 j = 9) :
    transferWords bookOrd true *ᵥ B64 j = transferWords bookOrd false *ᵥ B64 j := by
  have h := sector39_agree
  rw [List.all_eq_true] at h
  have hj' := h _ (sector39_list j hj)
  rw [beq_iff_eq] at hj'
  apply smul_right_injective _ (by norm_num : (6 : ℂ) ≠ 0)
  simp only
  rw [← Matrix.smul_mulVec, ← Matrix.smul_mulVec, B64_eq, ← transfer6_toFock,
    ← transfer6_toFock]
  exact Vec.toFock_eq_of_trie_eq numbering hj'

/-- With three or nine quarks the two transfers agree. -/
theorem agree_on_sector (N : ℕ) (hN : N = 3 ∨ N = 9) (v : Finset EM → ℂ)
    (hv : v ∈ LinearMap.range Φ64 ⊓ Fock.numberSector EM N) :
    transferWords bookOrd true *ᵥ v = transferWords bookOrd false *ᵥ v := by
  obtain ⟨⟨a, rfl⟩, hN'⟩ := hv
  rw [mulVec_Φ64, mulVec_Φ64]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : nq64 j = N
  · rw [agree39 j (by rw [hj]; exact hN)]
  · rw [coeff_eq_zero N a hN' j hj, zero_smul, zero_smul]

theorem sec39_eq (N : ℕ) (hN : N = 3 ∨ N = 9) :
    LinearMap.range Φ36 ⊓ Fock.numberSector EM N =
      LinearMap.range Φ64 ⊓ Fock.numberSector EM N := by
  refine Submodule.eq_of_le_of_finrank_eq (inf_le_inf_right _ range_Φ36_le) ?_
  rw [secC_card, secR_card']
  obtain ⟨h3, h9, -⟩ := countC
  obtain ⟨r3, r9⟩ := countR_3_9
  rcases hN with rfl | rfl
  · simp only [Nat.cast_ofNat]
    rw [h3, r3]
  · simp only [Nat.cast_ofNat]
    rw [h9, r9]

open Classical in
theorem tableC_39 (N : ℕ) (hN : N = 3 ∨ N = 9) (μ : ℂ) :
    finrank ℂ ↥(LinearMap.range Φ36 ⊓ Fock.numberSector EM N ⊓
      Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd false)) μ) =
      if μ = 6 ∨ μ = -6 then 4 else 0 := by
  have heq : LinearMap.range Φ36 ⊓ Fock.numberSector EM N ⊓
      Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd false)) μ =
      LinearMap.range Φ64 ⊓ Fock.numberSector EM N ⊓
      Module.End.eigenspace (Matrix.toLin' (transferWords bookOrd true)) μ := by
    rw [sec39_eq N hN]
    ext v
    constructor
    · rintro ⟨hs, he⟩
      refine ⟨hs, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at he ⊢
      rw [agree_on_sector N hN v hs, he]
    · rintro ⟨hs, he⟩
      refine ⟨hs, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at he ⊢
      rw [← agree_on_sector N hN v hs, he]
  rw [heq]
  exact tableR_pm6 N (by rcases hN with rfl | rfl <;> simp) μ

/-- `L` vanishes on the sectors outside the table, complex triplets. -/
theorem tableC_zero (N : ℕ) (hN : N ∉ ({3, 5, 6, 7, 9} : Set ℕ)) (v : Finset EM → ℂ)
    (hv : v ∈ LinearMap.range Φ36 ⊓ Fock.numberSector EM N) :
    Matrix.toLin' (transferWords bookOrd false) v = 0 := by
  rw [numberSector_eq] at hv
  have hle := inf_le_ker (d := 6) (by norm_num) Φ36 Φ36_injective
    (Matrix.toLin' numberOp) (Matrix.toLin' numberOp)
    (Matrix.toLin' ((6 : ℂ) • transferWords bookOrd false)) _ _ transferCCols
    (transferCEig.map Prod.snd) (fun a => by rw [Matrix.toLin'_apply, number_lc36])
    (fun a => by rw [Matrix.toLin'_apply, number_lc36])
    (fun a => by rw [Matrix.toLin'_apply, transferC_lc]) _ _ _ _
    (diagC 0 _ transferC_eig0) (diagC 0 _ transferC_eig0) invC.1 invC.2 (N : ℂ) (N : ℂ)
    keysC_eig (fun k h₁ _ => nullC k ?_)
  · have h6 := hle ⟨hv, hv.2⟩
    rw [Module.End.mem_eigenspace_iff, zero_smul, Matrix.toLin'_apply, Matrix.smul_mulVec] at h6
    rw [Matrix.toLin'_apply]
    exact (smul_eq_zero.mp h6).resolve_left (by norm_num)
  · have hk : nuC 0 k = N := by exact_mod_cast h₁
    obtain ⟨-, -, -, -, -, -, -, hall, h012⟩ := countC
    refine h012 k ?_
    by_contra hne
    refine hall k fun hmem => hne ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    omega

open Classical in
theorem tableC : Table (LinearMap.range Φ36) (Matrix.toLin' (transferWords bookOrd false))
    false := by
  refine ⟨fun N hN μ => tableC_39 N ?_ μ, fun N hN => ?_, fun μ => ?_,
    fun N hN v hv => tableC_zero N hN v hv⟩
  · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hN
  · simp only [Bool.false_eq_true, ite_false]
    rw [← Submodule.finrank_eq_zero, secC_card]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    obtain ⟨-, -, h5, h7, -⟩ := countC
    rcases hN with rfl | rfl
    · simp only [Nat.cast_ofNat]
      exact h5
    · simp only [Nat.cast_ofNat]
      exact h7
  · simp only [Bool.false_eq_true, ite_false]
    by_cases hp : μ = ((12 * Real.sqrt 2 : ℝ) : ℂ)
    · rw [ite_eq_left (Or.inl hp), hp]
      have h := tableC6_pm 1 (Or.inl rfl)
      rwa [one_mul] at h
    by_cases hm : μ = -((12 * Real.sqrt 2 : ℝ) : ℂ)
    · rw [ite_eq_left (Or.inr hm), hm]
      have h := tableC6_pm (-1) (Or.inr rfl)
      rwa [neg_one_mul] at h
    rw [ite_eq_right (by tauto)]
    by_cases h0 : μ = 0
    · rw [ite_eq_left h0, h0]
      exact tableC6_zero
    rw [ite_eq_right h0]
    exact tableC6_other μ h0 hp hm

/-! ### Every order of the modes -/

theorem numberSector_map (E : (Finset EM → ℂ) ≃ₗ[ℂ] (Finset EM → ℂ))
    (hE : E.conj (Matrix.toLin' numberOp) = Matrix.toLin' numberOp) (N : ℕ) :
    (Fock.numberSector EM N).map E.toLinearMap = Fock.numberSector EM N := by
  rw [numberSector_eq, map_eigenspace_conj, hE]

theorem sig_conj_number (ord₁ ord₂ : LinearOrder EM) :
    (sigEquiv ord₁ ord₂).conj (Matrix.toLin' numberOp) = Matrix.toLin' numberOp := by
  rw [← toLin'_conj, numberOp, Fock.orderSigma_conj_diagonal]

open Classical in
/-- The table moved by a linear equivalence that keeps the number of quarks. -/
theorem Table.map {Z : Submodule ℂ (Finset EM → ℂ)} {L : Module.End ℂ (Finset EM → ℂ)}
    {real : Bool} (E : (Finset EM → ℂ) ≃ₗ[ℂ] (Finset EM → ℂ))
    (hE : E.conj (Matrix.toLin' numberOp) = Matrix.toLin' numberOp) (h : Table Z L real) :
    Table (Z.map E.toLinearMap) (E.conj L) real := by
  have hsec : ∀ N, Z.map E.toLinearMap ⊓ Fock.numberSector EM N =
      (Z ⊓ Fock.numberSector EM N).map E.toLinearMap := fun N => by
    rw [map_inf_equiv, numberSector_map E hE]
  have hfin : ∀ N μ, finrank ℂ ↥(Z.map E.toLinearMap ⊓ Fock.numberSector EM N ⊓
      Module.End.eigenspace (E.conj L) μ) =
      finrank ℂ ↥(Z ⊓ Fock.numberSector EM N ⊓ Module.End.eigenspace L μ) := fun N μ => by
    rw [hsec, ← map_eigenspace_conj, ← map_inf_equiv, LinearEquiv.finrank_map_eq]
  dsimp only [Table] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun N hN μ => by rw [hfin]; exact h1 N hN μ, fun N hN => ?_,
    fun μ => by rw [hfin]; exact h3 μ, fun N hN v hv => ?_⟩
  · have h2' := h2 N hN
    cases real
    · simp only [Bool.false_eq_true, ite_false] at h2' ⊢
      rw [hsec, h2', Submodule.map_bot]
    · simp only [ite_true] at h2' ⊢
      intro μ
      rw [hfin]
      exact h2' μ
  · rw [hsec] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      h4 N hN w hw, map_zero]

open Classical in
/-- The table for an operator that agrees on the sector with one that has it. -/
theorem Table.congr {Z : Submodule ℂ (Finset EM → ℂ)} {L L' : Module.End ℂ (Finset EM → ℂ)}
    {real : Bool} (hL : ∀ v ∈ Z, L v = L' v) (h : Table Z L real) : Table Z L' real := by
  have heig : ∀ N μ, Z ⊓ Fock.numberSector EM N ⊓ Module.End.eigenspace L μ =
      Z ⊓ Fock.numberSector EM N ⊓ Module.End.eigenspace L' μ := fun N μ => by
    ext v
    constructor
    · rintro ⟨hs, he⟩
      refine ⟨hs, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at he ⊢
      rw [← hL v hs.1, he]
    · rintro ⟨hs, he⟩
      refine ⟨hs, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at he ⊢
      rw [hL v hs.1, he]
  dsimp only [Table] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun N hN μ => by rw [← heig]; exact h1 N hN μ, fun N hN => ?_,
    fun μ => by rw [← heig]; exact h3 μ, fun N hN v hv => by rw [← hL v hv.1]; exact h4 N hN v hv⟩
  have h2' := h2 N hN
  cases real
  · simp only [Bool.false_eq_true, ite_false] at h2' ⊢
    exact h2'
  · simp only [ite_true] at h2' ⊢
    intro μ
    rw [← heig]
    exact h2' μ

theorem transferWords_change (ord₁ ord₂ : LinearOrder EM) (real : Bool) :
    transferWords ord₂ real =
      Fock.orderSigma ord₁ ord₂ * transferWords ord₁ real * (Fock.orderSigma ord₁ ord₂)⁻¹ := by
  cases real <;>
  simp only [transferWords, transferOf, hopA_change ord₁ ord₂, Fock.orderSigma_conj_conjTranspose,
    Fock.orderSigma_conj_mul, Fock.orderSigma_conj_add, Fock.orderSigma_conj_sum,
    Fock.orderSigma_conj_smul, Bool.false_eq_true, ite_false, ite_true]

open Classical in
/-- The table of the words in every order of the modes. -/
theorem table_words (Z : Submodule ℂ (Finset EM → ℂ)) (real : Bool)
    (h : Table Z (Matrix.toLin' (transferWords bookOrd real)) real) (ord : LinearOrder EM) :
    Table (Z.map (sigEquiv bookOrd ord).toLinearMap)
      (Matrix.toLin' (transferWords ord real)) real := by
  rw [transferWords_change bookOrd ord, toLin'_conj]
  exact h.map _ (sig_conj_number bookOrd ord)

end TransferSpectra

end Artform
