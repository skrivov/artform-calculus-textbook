import ArtformTextbook.Ch12.ModelsSymmetry

/-!
# The two-baryon sector: sixteen products of two quartets

The zero-flux values with three quarks at each end are, in the book's order, the span of the
sixteen products of two quartets (`ModelsCheck.Z33_cube` and its companions, the same space for
the five models). On them `3 Ω`, `2 S_z` and `4 S²` are the matrices of the certificate
(`ModelsCheck.block3_lc`, `ModelsCheck.blockSz_lc`, `ModelsCheck.blockSq_lc`), whose common
eigenvectors the kernel has checked; the multiplicities of the joint values follow
(`ModelsCheck.ladder_book`), and hold in every order of the modes
(`ModelsCheck.ladder_change`).
-/

namespace Artform

open scoped Matrix

open Module FockCalc ModelsData SpecCert ModelsCheck Edge

namespace ModelsCheck

/-! ### The sixteen products -/

/-- The place among the sixty-four of the product of the quartet members `a` at `x` and `b` at
`y`, numbered `4 a + b`. -/
def blockIdx (l : Fin 16) : Fin 64 := ⟨8 * (l / 4 + 2) + (l % 4 + 2), by omega⟩

/-- The sixteen products of two quartets. -/
noncomputable def B16 (l : Fin 16) : Finset EM → ℂ := B64 (blockIdx l)

theorem B16_eq (l : Fin 16) : B16 l = Vec.toFock code (blockVec l) := by
  rw [B16, B64_eq, blockVec]
  congr 2
  simp only [blockIdx]
  omega

/-- Coefficients over the sixteen products, to the coefficient table they combine. -/
noncomputable def Φ16 : (Fin 16 → ℂ) →ₗ[ℂ] (Finset EM → ℂ) := Fintype.linearCombination ℂ B16

theorem blockIdx_injective : Function.Injective blockIdx := by decide

theorem B16_linearIndependent : LinearIndependent ℂ B16 :=
  B64_linearIndependent.comp _ blockIdx_injective

theorem Φ16_injective : Function.Injective Φ16 := injective_of_li B16_linearIndependent

/-- The products in the statement's indexing, `(a, b) ↦ q(a) ⊗ q(b)`. -/
theorem prod_quartet_eq (p : Fin 4 × Fin 4) :
    prod (Vertex.quartet Vertex.bookOrd p.1) (Vertex.quartet Vertex.bookOrd p.2) =
      B16 (finProdFinEquiv p) := by
  obtain ⟨a, b⟩ := p
  fin_cases a <;> fin_cases b <;> rfl

theorem range_prod_quartet :
    Set.range (fun p : Fin 4 × Fin 4 =>
      prod (Vertex.quartet Vertex.bookOrd p.1) (Vertex.quartet Vertex.bookOrd p.2)) =
      Set.range B16 := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨_, (prod_quartet_eq p).symm⟩
  · rintro ⟨l, rfl⟩
    refine ⟨finProdFinEquiv.symm l, ?_⟩
    simp only [prod_quartet_eq, Equiv.apply_symm_apply]

theorem linearIndependent_prod_quartet :
    LinearIndependent ℂ (fun p : Fin 4 × Fin 4 =>
      prod (Vertex.quartet Vertex.bookOrd p.1) (Vertex.quartet Vertex.bookOrd p.2)) := by
  have : (fun p : Fin 4 × Fin 4 =>
      prod (Vertex.quartet Vertex.bookOrd p.1) (Vertex.quartet Vertex.bookOrd p.2)) =
      B16 ∘ finProdFinEquiv := funext prod_quartet_eq
  rw [this]
  exact B16_linearIndependent.comp _ finProdFinEquiv.injective

/-! ### The sector with three quarks at each end -/

/-- The products with three quarks at each end. -/
def blockSet : Finset (Fin 64) := Finset.univ.filter fun j => nq (j / 8) = 3 ∧ nq (j % 8) = 3

theorem blockSet_eq : blockSet = Finset.univ.image blockIdx := by decide

theorem range_Φ16 : LinearMap.range Φ16 = Submodule.span ℂ (Set.range B16) :=
  Fintype.range_linearCombination ℂ B16

theorem Z33_cube_eq :
    LinearMap.range Φ64 ⊓ endSector (Fin 3) (Fin 2) 3 3 = LinearMap.range Φ16 := by
  rw [Φ64, range_inf_eq_span B64 B64_linearIndependent _
      (fun t => t.toLeft.card = 3 ∧ t.toRight.card = 3) (fun _ => Iff.rfl) blockSet ?_ ?_,
    range_Φ16, blockSet_eq, Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp]
  · rfl
  · intro j hj
    simp only [blockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have h := B64_mem_endSector j
    rwa [hj.1, hj.2] at h
  · intro j hj t ht
    simp only [blockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact B64_apply_endSector j fun h => hj ⟨h.1 ▸ ht.1, h.2 ▸ ht.2⟩

theorem Z33_cube : zeroFluxValues cubeTriplet bookOrd ⊓ endSector (Fin 3) (Fin 2) 3 3 =
    LinearMap.range Φ16 := by
  rw [zeroFluxValues_cube, Z33_cube_eq]

theorem Z33_ico : zeroFluxValues icoTriplet bookOrd ⊓ endSector (Fin 3) (Fin 2) 3 3 =
    LinearMap.range Φ16 := by
  rw [zeroFluxValues_ico, Z33_cube_eq]

theorem B36_eq_B64 (j : Fin 36) :
    B36 j = B64 ⟨8 * Vertex.sixToEight (pairOf36 j).1 + Vertex.sixToEight (pairOf36 j).2,
      by omega⟩ := by
  rw [B36, B64, sixProd, eightProd, Vertex.six_eq, Vertex.six_eq]
  congr 3 <;> simp only [pairOf] <;> apply Fin.ext <;> simp <;> omega

theorem range_Φ36_le : LinearMap.range Φ36 ≤ LinearMap.range Φ64 := by
  rw [Φ36, Φ64, Fintype.range_linearCombination, Fintype.range_linearCombination]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨_, (B36_eq_B64 j).symm⟩

theorem B16_mem_Φ36 (l : Fin 16) : B16 l ∈ LinearMap.range Φ36 := by
  rw [Φ36, Fintype.range_linearCombination]
  refine Submodule.subset_span ⟨⟨6 * (l / 4 + 1) + (l % 4 + 1), by omega⟩, ?_⟩
  rw [B36_eq_B64, B16]
  congr 1
  apply Fin.ext
  revert l
  decide

theorem Z33_36_eq :
    LinearMap.range Φ36 ⊓ endSector (Fin 3) (Fin 2) 3 3 = LinearMap.range Φ16 := by
  apply le_antisymm
  · rw [← Z33_cube_eq]
    exact inf_le_inf_right _ range_Φ36_le
  · refine le_inf ?_ ?_
    · rw [range_Φ16, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact B16_mem_Φ36 l
    · rw [← Z33_cube_eq]
      exact inf_le_right

theorem Z33_c3a5 : zeroFluxValues c3a5Triplet bookOrd ⊓ endSector (Fin 3) (Fin 2) 3 3 =
    LinearMap.range Φ16 := by
  rw [zeroFluxValues_c3a5, Z33_36_eq]

theorem Z33_valentiner :
    zeroFluxValues valentinerTriplet bookOrd ⊓ endSector (Fin 3) (Fin 2) 3 3 =
      LinearMap.range Φ16 := by
  rw [zeroFluxValues_valentiner, Z33_36_eq]

theorem Z33_su3 : zeroFluxValues su3Triplet bookOrd ⊓ endSector (Fin 3) (Fin 2) 3 3 =
    LinearMap.range Φ16 := by
  rw [zeroFluxValues_su3, Z33_36_eq]

/-! ### The operators on the sixteen products -/

theorem block_keys3 : ∀ l : Fin 16, keysLt 16 (block3Cols.getD l []) = true := by decide +kernel

theorem block_keysZ : ∀ l : Fin 16, keysLt 16 (blockSzCols.getD l []) = true := by
  decide +kernel

theorem block_keysQ : ∀ l : Fin 16, keysLt 16 (blockSqCols.getD l []) = true := by
  decide +kernel

theorem block3_cols0 : (List.range 16).all (colCheck tally0C block3Cols blockVec) = true := by
  decide +kernel

theorem block3_lc (a : Fin 16 → ℂ) :
    ((3 : ℂ) • tally bookOrd 1) *ᵥ Φ16 a = Φ16 (colMat 4 16 block3Cols *ᵥ a) :=
  op_lc (d := 4) (by norm_num) (by norm_num) (tally3Op 1) _ tally3Op_one block3Cols blockVec
    B16 B16_eq block_keys3 (fun l => by
      have := block3_cols
      rw [all_range_iff] at this
      exact this l l.2) a

theorem block3_lc0 (a : Fin 16 → ℂ) :
    ((3 : ℂ) • tally bookOrd 0) *ᵥ Φ16 a = Φ16 (colMat 4 16 block3Cols *ᵥ a) :=
  op_lc (d := 4) (by norm_num) (by norm_num) (tally3Op 0) _ tally3Op_zero block3Cols blockVec
    B16 B16_eq block_keys3 (fun l => by
      have := block3_cols0
      rw [all_range_iff] at this
      exact this l l.2) a

theorem blockSz_lc (a : Fin 16 → ℂ) :
    ((2 : ℂ) • spinZ) *ᵥ Φ16 a = Φ16 (colMat 4 16 blockSzCols *ᵥ a) := by
  rw [two_spinZ]
  exact diag_lc (d := 4) (by norm_num) (by norm_num) _ spinZ2 spinZ2_spec blockSzCols blockVec
    B16 B16_eq block_keysZ (fun l => by
      have := blockSz_cols
      rw [all_range_iff] at this
      exact this l l.2) a

theorem blockSq_lc (a : Fin 16 → ℂ) :
    ((4 : ℂ) • spinSq bookOrd) *ᵥ Φ16 a = Φ16 (colMat 4 16 blockSqCols *ᵥ a) := by
  refine mulVec_linearCombination (d := 4) (by norm_num) (by norm_num) _ B16 blockSqCols
    block_keysQ (fun l => ?_) a
  have hc : sqCheck l = true := by
    have := blockSq_cols
    rw [all_range_iff] at this
    exact this l l.2
  rw [B16_eq, Matrix.smul_mulVec, spinSq_toFock,
    Vec.toFock_eq_of_trie_eq numbering (by simpa only [sqCheck, beq_iff_eq] using hc),
    toFock_combo_basis (by norm_num) blockVec B16 B16_eq _ (block_keysQ l)]

/-! ### The common eigenvectors -/

/-- The values of the certificate: `3 Ω` (`r = 0`), `2 S_z` (`r = 1`) and `4 S²` (`r = 2`). -/
def nuB (r : ℕ) (k : Fin 16) : ℤ := ((blockEigOf r).getD k (0, [])).1

theorem block_inv1 : invOK 4 16 blockD (blockEigOf 1) blockDg = true := by decide +kernel

theorem block_inv2 : invOK 4 16 blockD (blockEigOf 2) blockDg = true := by decide +kernel

theorem blockEigOf_snd (r : ℕ) : (blockEigOf r).map Prod.snd = blockEig.map Prod.snd := by
  simp only [blockEigOf, List.map_map]
  rfl

theorem block_diag (r : ℕ) (cols : List Vec) (h : eigOK 4 16 cols (blockEigOf r) = true) :
    colMat 4 16 cols * Cmat 4 16 (blockEig.map Prod.snd) =
      Cmat 4 16 (blockEig.map Prod.snd) * Matrix.diagonal fun k => (nuB r k : ℂ) := by
  rw [← blockEigOf_snd r]
  exact colMat_mul_Cmat (by norm_num) cols _ h

theorem block_D :
    colMat 4 16 blockD * Cmat 4 16 (blockEig.map Prod.snd) =
      Matrix.diagonal (fun k : Fin 16 => (blockDg.getD k 0 : ℂ)) ∧
        ∀ k : Fin 16, (blockDg.getD k 0 : ℂ) ≠ 0 := by
  rw [← blockEigOf_snd 0]
  exact D_mul_Cmat (by norm_num) _ _ _ _ block_eig3 block_inv

/-- The value pairs `(2 S_z, 3 Ω)` of the sixteen eigenvectors. -/
def zPairs : List (ℤ × ℤ) :=
  [(-6, 0), (-4, 0), (-4, 12), (-2, 0), (-2, 12), (-2, 20), (0, 0), (0, 12), (0, 20), (0, 24),
    (2, 0), (2, 12), (2, 20), (4, 0), (4, 12), (6, 0)]

theorem zPairs_cover : ∀ k : Fin 16, (nuB 1 k, nuB 0 k) ∈ zPairs := by decide +kernel

theorem zPairs_reached : ∀ p ∈ zPairs, ∃ k : Fin 16, (nuB 1 k, nuB 0 k) = p := by decide +kernel

theorem nuB1_counts : ∀ s : ℤ, |s| ≤ 3 →
    (Finset.univ.filter fun k => nuB 1 k = 2 * s).card = 4 - s.natAbs := by
  intro s hs
  have h1 : -3 ≤ s := by rw [abs_le] at hs; exact hs.1
  have h2 : s ≤ 3 := by rw [abs_le] at hs; exact hs.2
  interval_cases s <;> decide +kernel

theorem nuB1_bound : ∀ k : Fin 16, -6 ≤ nuB 1 k ∧ nuB 1 k ≤ 6 := by decide +kernel

/-- The value pairs `(4 S², 3 Ω)`: spin `3, 2, 1, 0` carry `0, 4, 20/3, 8`. -/
theorem sq_ladder : ∀ k : Fin 16,
    (nuB 2 k = 48 → nuB 0 k = 0) ∧ (nuB 2 k = 24 → nuB 0 k = 12) ∧
    (nuB 2 k = 8 → nuB 0 k = 20) ∧ (nuB 2 k = 0 → nuB 0 k = 24) := by
  decide +kernel

theorem nuB2_counts :
    (Finset.univ.filter fun k => nuB 2 k = 48).card = 7 ∧
    (Finset.univ.filter fun k => nuB 2 k = 24).card = 5 ∧
    (Finset.univ.filter fun k => nuB 2 k = 8).card = 3 ∧
    (Finset.univ.filter fun k => nuB 2 k = 0).card = 1 := by
  decide +kernel

theorem blockZ3_comm :
    colMat 4 16 block3Cols * colMat 4 16 blockSzCols =
      colMat 4 16 blockSzCols * colMat 4 16 block3Cols :=
  colMat_mul_eq_of_check (by norm_num) _ _ _ _ block_keysZ block_keys3 (by decide +kernel)

/-! ### Eigenspaces read in a basis -/

theorem toLin'_smul_eigenspace (X : Matrix (Finset EM) (Finset EM) ℂ) {c : ℂ} (hc : c ≠ 0)
    (μ : ℂ) :
    Module.End.eigenspace (Matrix.toLin' (c • X)) (c * μ) =
      Module.End.eigenspace (Matrix.toLin' X) μ := by
  rw [map_smul, eigenspace_smul _ hc]

/-- An eigenspace on `W` lies in another when it does for the matrices in a basis of `W`. -/
theorem inf_eigenspace_le {n : ℕ} (W : Submodule ℂ (Finset EM → ℂ))
    (Φ : (Fin n → ℂ) →ₗ[ℂ] (Finset EM → ℂ)) (hΦ : Function.Injective Φ)
    (hW : LinearMap.range Φ = W) (T₁ T₂ : Module.End ℂ (Finset EM → ℂ))
    (K₁ K₂ : Matrix (Fin n) (Fin n) ℂ) (hT₁ : ∀ a, T₁ (Φ a) = Φ (K₁ *ᵥ a))
    (hT₂ : ∀ a, T₂ (Φ a) = Φ (K₂ *ᵥ a)) (μ₁ μ₂ : ℂ)
    (hK : Module.End.eigenspace (Matrix.toLin' K₂) μ₂ ≤
      Module.End.eigenspace (Matrix.toLin' K₁) μ₁) :
    W ⊓ Module.End.eigenspace T₂ μ₂ ≤ Module.End.eigenspace T₁ μ₁ := by
  intro v hv
  obtain ⟨hvW, hv⟩ := Submodule.mem_inf.mp hv
  rw [← hW] at hvW
  obtain ⟨a, rfl⟩ := hvW
  rw [Module.End.mem_eigenspace_iff, hT₂, ← map_smul] at hv
  have ha : a ∈ Module.End.eigenspace (Matrix.toLin' K₂) μ₂ := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hΦ hv
  have ha' := hK ha
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at ha'
  rw [Module.End.mem_eigenspace_iff, hT₁, ha', map_smul]

/-! ### The claims of Proposition 12.5 on a sector -/

/-- The claims of Proposition 12.5 on a sector `Z` with a tally `X` and the spin operators `S_z`
and `S²` (the body of the statement's `ladder`). -/
def Ladder (Sz S2 X : Module.End ℂ (Finset EM → ℂ)) (Z : Submodule ℂ (Finset EM → ℂ)) : Prop :=
  let values : ℤ → Set ℂ := fun s =>
    if s = 3 then {0} else if s = 2 then {0, 4} else if s = 1 then {0, 4, 20 / 3}
    else {0, 4, 20 / 3, 8}
  (∀ v ∈ Z, X (Sz v) = Sz (X v)) ∧
  (∀ s : ℤ, finrank ℂ ↥(Z ⊓ Module.End.eigenspace Sz (s : ℂ)) =
    if |s| ≤ 3 then 4 - s.natAbs else 0) ∧
  (∀ s : ℤ, |s| ≤ 3 → ∀ μ : ℂ,
    Z ⊓ Module.End.eigenspace Sz (s : ℂ) ⊓ Module.End.eigenspace X μ ≠ ⊥ ↔ μ ∈ values |s|) ∧
  finrank ℂ ↥(Z ⊓ Module.End.eigenspace S2 12) = 7 ∧
  Z ⊓ Module.End.eigenspace S2 12 ≤ Module.End.eigenspace X 0 ∧
  finrank ℂ ↥(Z ⊓ Module.End.eigenspace S2 6) = 5 ∧
  Z ⊓ Module.End.eigenspace S2 6 ≤ Module.End.eigenspace X 4 ∧
  finrank ℂ ↥(Z ⊓ Module.End.eigenspace S2 2) = 3 ∧
  Z ⊓ Module.End.eigenspace S2 2 ≤ Module.End.eigenspace X (20 / 3) ∧
  finrank ℂ ↥(Z ⊓ Module.End.eigenspace S2 0) = 1 ∧
  Z ⊓ Module.End.eigenspace S2 0 ≤ Module.End.eigenspace X 8

/-- The claims move with a linear equivalence that conjugates the operators. -/
theorem Ladder.map {Sz S2 X : Module.End ℂ (Finset EM → ℂ)} {Z : Submodule ℂ (Finset EM → ℂ)}
    (h : Ladder Sz S2 X Z) (E : (Finset EM → ℂ) ≃ₗ[ℂ] (Finset EM → ℂ)) :
    Ladder (E.conj Sz) (E.conj S2) (E.conj X) (Z.map E.toLinearMap) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have hfin : ∀ (A : Submodule ℂ (Finset EM → ℂ)) (T : Module.End ℂ (Finset EM → ℂ)) (μ : ℂ),
      Z.map E.toLinearMap ⊓ Module.End.eigenspace (E.conj T) μ =
        (Z ⊓ Module.End.eigenspace T μ).map E.toLinearMap := by
    intro _ T μ
    rw [map_inf_equiv, map_eigenspace_conj]
  have hle : ∀ (T T' : Module.End ℂ (Finset EM → ℂ)) (μ μ' : ℂ),
      Z ⊓ Module.End.eigenspace T μ ≤ Module.End.eigenspace T' μ' →
        Z.map E.toLinearMap ⊓ Module.End.eigenspace (E.conj T) μ ≤
          Module.End.eigenspace (E.conj T') μ' := by
    intro T T' μ μ' hTT
    rw [hfin Z T μ, ← map_eigenspace_conj]
    exact Submodule.map_mono hTT
  refine ⟨?_, ?_, ?_, ?_, hle _ _ _ _ h5, ?_, hle _ _ _ _ h7, ?_, hle _ _ _ _ h9, ?_,
    hle _ _ _ _ h11⟩
  · rintro _ ⟨w, hw, rfl⟩
    simp only [LinearEquiv.coe_coe, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
      h1 w hw]
  · intro s
    rw [hfin Z Sz, LinearEquiv.finrank_map_eq, h2]
  · intro s hs μ
    rw [← h3 s hs μ, hfin Z Sz, ← map_eigenspace_conj, ← map_inf_equiv, Ne, Ne,
      Submodule.map_eq_bot_iff]
  · rw [hfin Z S2, LinearEquiv.finrank_map_eq, h4]
  · rw [hfin Z S2, LinearEquiv.finrank_map_eq, h6]
  · rw [hfin Z S2, LinearEquiv.finrank_map_eq, h8]
  · rw [hfin Z S2, LinearEquiv.finrank_map_eq, h10]

/-! ### The claims in the book's order -/

theorem nuB_cast_eq {r : ℕ} {k : Fin 16} {w : ℤ} {μ c : ℂ} (h : c * μ = w) :
    (nuB r k : ℂ) = c * μ ↔ nuB r k = w := by
  rw [h, Int.cast_inj]

theorem cast_eq_three_mul (c : ℤ) (μ : ℂ) : ((c : ℂ) = 3 * μ) ↔ μ = (c : ℂ) / 3 := by
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rw [h]
    ring

theorem ladder_values (s : ℤ) (hs : |s| ≤ 3) (μ : ℂ) :
    (∃ k : Fin 16, nuB 1 k = 2 * s ∧ (nuB 0 k : ℂ) = 3 * μ) ↔
      μ ∈ (if |s| = 3 then ({0} : Set ℂ) else if |s| = 2 then {0, 4}
        else if |s| = 1 then {0, 4, 20 / 3} else {0, 4, 20 / 3, 8}) := by
  have hp : (∃ k : Fin 16, nuB 1 k = 2 * s ∧ (nuB 0 k : ℂ) = 3 * μ) ↔
      ∃ p ∈ zPairs, p.1 = 2 * s ∧ μ = (p.2 : ℂ) / 3 := by
    constructor
    · rintro ⟨k, hk1, hk2⟩
      exact ⟨_, zPairs_cover k, hk1, (cast_eq_three_mul _ _).mp hk2⟩
    · rintro ⟨p, hp, h1, h2⟩
      rcases zPairs_reached p hp with ⟨k, rfl⟩
      exact ⟨k, h1, (cast_eq_three_mul _ _).mpr h2⟩
  rw [hp]
  have h1 : -3 ≤ s := by rw [abs_le] at hs; exact hs.1
  have h2 : s ≤ 3 := by rw [abs_le] at hs; exact hs.2
  simp only [zPairs, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  interval_cases s <;> norm_num

/-- The claims of Proposition 12.5 on the sixteen products, in the book's order, for a tally whose
matrix on them is that of the certificate. -/
theorem ladder_book (X : Matrix (Finset EM) (Finset EM) ℂ)
    (hX : ∀ a, ((3 : ℂ) • X) *ᵥ Φ16 a = Φ16 (colMat 4 16 block3Cols *ᵥ a)) :
    Ladder (Matrix.toLin' spinZ) (Matrix.toLin' (spinSq bookOrd)) (Matrix.toLin' X)
      (LinearMap.range Φ16) := by
  have h3C := block_diag 0 block3Cols block_eig3
  have hzC := block_diag 1 blockSzCols block_eigSz
  have hqC := block_diag 2 blockSqCols block_eigSq
  obtain ⟨hDC, hdg⟩ := block_D
  have hT3 : ∀ a, Matrix.toLin' ((3 : ℂ) • X) (Φ16 a) =
      Φ16 (colMat 4 16 block3Cols *ᵥ a) := fun a => by rw [Matrix.toLin'_apply, hX]
  have hTz : ∀ a, Matrix.toLin' ((2 : ℂ) • spinZ) (Φ16 a) =
      Φ16 (colMat 4 16 blockSzCols *ᵥ a) := fun a => by rw [Matrix.toLin'_apply, blockSz_lc]
  have hTq : ∀ a, Matrix.toLin' ((4 : ℂ) • spinSq bookOrd) (Φ16 a) =
      Φ16 (colMat 4 16 blockSqCols *ᵥ a) := fun a => by rw [Matrix.toLin'_apply, blockSq_lc]
  have e3 : ∀ b, Matrix.toLin' X (Φ16 b) = (1 / 3 : ℂ) • Φ16 (colMat 4 16 block3Cols *ᵥ b) := by
    intro b
    rw [← hT3, map_smul, LinearMap.smul_apply, smul_smul]
    norm_num
  have ez : ∀ b, Matrix.toLin' spinZ (Φ16 b) =
      (1 / 2 : ℂ) • Φ16 (colMat 4 16 blockSzCols *ᵥ b) := by
    intro b
    rw [← hTz, map_smul, LinearMap.smul_apply, smul_smul]
    norm_num
  have hS2 : ∀ (lam : ℂ) (w : ℤ), 4 * lam = w →
      finrank ℂ ↥(LinearMap.range Φ16 ⊓ Module.End.eigenspace (Matrix.toLin' (spinSq bookOrd))
        lam) = (Finset.univ.filter fun k => nuB 2 k = w).card := by
    intro lam w hw
    rw [← toLin'_smul_eigenspace _ (by norm_num : (4 : ℂ) ≠ 0) lam,
      finrank_inf_eigenspace _ _ Φ16 Φ16_injective rfl _ hTq,
      finrank_eigenspace_colMat (by norm_num) blockSqCols blockD (blockEigOf 2) blockDg block_eigSq
        block_inv2]
    exact card_filter_cast (nuB 2) hw
  have hle : ∀ (lam μ : ℂ) (w v : ℤ), 4 * lam = w → 3 * μ = v →
      (∀ k, nuB 2 k = w → nuB 0 k = v) →
      LinearMap.range Φ16 ⊓ Module.End.eigenspace (Matrix.toLin' (spinSq bookOrd)) lam ≤
        Module.End.eigenspace (Matrix.toLin' X) μ := by
    intro lam μ w v hw hv hk
    rw [← toLin'_smul_eigenspace _ (by norm_num : (4 : ℂ) ≠ 0) lam,
      ← toLin'_smul_eigenspace X three_ne_zero μ]
    refine inf_eigenspace_le _ Φ16 Φ16_injective rfl _ _ _ _ hT3 hTq _ _
      (eigenspace_le_of_diag _ _ _ _ _ _ _ h3C hqC hDC hdg _ _ fun k hk' => ?_)
    rw [hw, Int.cast_inj] at hk'
    rw [hv, hk k hk']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    rw [ez, map_smul, e3, e3, map_smul, ez, smul_smul, smul_smul, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, blockZ3_comm, mul_comm (1 / 3 : ℂ)]
  · intro s
    rw [← toLin'_smul_eigenspace spinZ two_ne_zero (s : ℂ),
      finrank_inf_eigenspace _ _ Φ16 Φ16_injective rfl _ hTz,
      finrank_eigenspace_colMat (by norm_num) blockSzCols blockD (blockEigOf 1) blockDg block_eigSz
        block_inv1]
    change (Finset.univ.filter fun k => (nuB 1 k : ℂ) = 2 * (s : ℂ)).card = _
    rw [card_filter_cast (nuB 1) (w := 2 * s) (by push_cast; ring)]
    split_ifs with hs
    · exact nuB1_counts s hs
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _ hk
      have := nuB1_bound k
      rw [abs_le] at hs
      omega
  · intro s hs μ
    rw [← toLin'_smul_eigenspace spinZ two_ne_zero (s : ℂ),
      ← toLin'_smul_eigenspace X three_ne_zero μ, Ne, ← Submodule.finrank_eq_zero,
      finrank_inf_inf_eigenspace _ _ _ Φ16 Φ16_injective rfl _ _ hTz hT3,
      finrank_inf_eigenspace_of_diag _ _ _ _ _ _ _ hzC h3C hDC hdg, ← Ne,
      Finset.card_ne_zero, Finset.filter_nonempty_iff]
    simp only [Finset.mem_univ, true_and]
    rw [← ladder_values s hs μ]
    refine exists_congr fun k => and_congr_left' ?_
    rw [show (2 : ℂ) * (s : ℂ) = ((2 * s : ℤ) : ℂ) by push_cast; ring, Int.cast_inj]
  · rw [hS2 12 48 (by norm_num)]
    exact nuB2_counts.1
  · exact hle 12 0 48 0 (by norm_num) (by norm_num) fun k => (sq_ladder k).1
  · rw [hS2 6 24 (by norm_num)]
    exact nuB2_counts.2.1
  · exact hle 6 4 24 12 (by norm_num) (by norm_num) fun k => (sq_ladder k).2.1
  · rw [hS2 2 8 (by norm_num)]
    exact nuB2_counts.2.2.1
  · exact hle 2 (20 / 3) 8 20 (by norm_num) (by norm_num) fun k => (sq_ladder k).2.2.1
  · rw [hS2 0 0 (by norm_num)]
    exact nuB2_counts.2.2.2
  · exact hle 0 8 0 24 (by norm_num) (by norm_num) fun k => (sq_ladder k).2.2.2

end ModelsCheck

namespace Edge

theorem endSector_map_sig (ord₁ ord₂ : LinearOrder EM) (a b : ℕ) :
    (endSector (Fin 3) (Fin 2) a b).map (sigEquiv ord₁ ord₂).toLinearMap =
      endSector (Fin 3) (Fin 2) a b := by
  ext v
  rw [Submodule.mem_map_equiv, sigEquiv_symm_apply, Fock.orderSigma_inv]
  change (∀ n, (Fock.orderSigma ord₁ ord₂ *ᵥ v) n ≠ 0 → _) ↔ ∀ n, v n ≠ 0 → _
  refine forall_congr' fun n => ?_
  rw [Fock.orderSigma, Matrix.mulVec_diagonal]
  have hs : Fock.orderSign ord₁ ord₂ n ≠ 0 := by
    rcases Fock.orderSign_eq_one_or ord₁ ord₂ n with h | h <;> rw [h] <;> norm_num
  rw [Ne, mul_eq_zero, not_or]
  exact ⟨fun h hv => h ⟨hs, hv⟩, fun h hv => h hv.2⟩

/-- The sector with three quarks at each end, in any order, moved from the book's order. -/
theorem Z33_change {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (ord : LinearOrder EM) :
    zeroFluxValues ρ ord ⊓ endSector (Fin 3) (Fin 2) 3 3 =
      (zeroFluxValues ρ bookOrd ⊓ endSector (Fin 3) (Fin 2) 3 3).map
        (sigEquiv bookOrd ord).toLinearMap := by
  rw [map_inf_equiv, endSector_map_sig, zeroFluxValues_change ρ bookOrd ord]

end Edge

namespace ModelsCheck

/-- The claims of Proposition 12.5 for a model whose sector with three quarks at each end is the
span of the sixteen products, in any order of the modes. -/
theorem ladder_ord {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : zeroFluxValues ρ bookOrd ⊓ endSector (Fin 3) (Fin 2) 3 3 = LinearMap.range Φ16)
    (m : ℕ) (hm : ∀ a, ((3 : ℂ) • tally bookOrd m) *ᵥ Φ16 a = Φ16 (colMat 4 16 block3Cols *ᵥ a))
    (ord : LinearOrder EM) :
    Ladder (Matrix.toLin' spinZ) (Matrix.toLin' (spinSq ord)) (Matrix.toLin' (tally ord m))
      (zeroFluxValues ρ ord ⊓ endSector (Fin 3) (Fin 2) 3 3) := by
  have h := (ladder_book _ hm).map (sigEquiv bookOrd ord)
  rw [← toLin'_conj, ← toLin'_conj, ← toLin'_conj, ← spinZ_change, ← spinSq_change,
    ← tally_change, ← hρ, ← Z33_change] at h
  exact h

theorem conj_mulVec_sig (ord₁ ord₂ : LinearOrder EM) (A : Matrix (Finset EM) (Finset EM) ℂ)
    (x : Finset EM → ℂ) :
    (Fock.orderSigma ord₁ ord₂ * A * (Fock.orderSigma ord₁ ord₂)⁻¹) *ᵥ
        (Fock.orderSigma ord₁ ord₂ *ᵥ x) = Fock.orderSigma ord₁ ord₂ *ᵥ (A *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Fock.orderSigma_inv_mul, Matrix.mul_one,
    Matrix.mulVec_mulVec]

/-- The tally with the pair hop and without it agree on the sector with three quarks at each
end. -/
theorem tally_one_eq_zero_Z33 (ord : LinearOrder EM) (v : Finset EM → ℂ)
    (hv : v ∈ zeroFluxValues cubeTriplet ord ⊓ endSector (Fin 3) (Fin 2) 3 3) :
    tally ord 1 *ᵥ v = tally ord 0 *ᵥ v := by
  rw [Z33_change, Z33_cube] at hv
  obtain ⟨w, ⟨a, rfl⟩, rfl⟩ := hv
  rw [LinearEquiv.coe_coe, sigEquiv_apply, tally_change bookOrd ord 1, tally_change bookOrd ord 0,
    conj_mulVec_sig, conj_mulVec_sig]
  congr 1
  apply eq_of_three_smul
  rw [← Matrix.smul_mulVec, ← Matrix.smul_mulVec, block3_lc, block3_lc0]

end ModelsCheck

end Artform

