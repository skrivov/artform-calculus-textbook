import ArtformTextbook.Ch12.ModelsBlock
import ArtformTextbook.Ch12.ModelsGroups
import ArtformTextbook.Ch12.Statements.Models

/-!
# The matter models on one edge: Propositions 12.1, 12.3, 12.5–12.7, 12.10, 12.12, Theorem 12.4

The proofs. The vertex invariants are those of `Ch12/VertexInvariants.lean`; the zero-flux
sectors, in the book's order of the modes, are the spans of the products of `Ch12/EdgeSector.lean`
(`Edge.zeroFluxValues_cube` and its companions), and the operators of the chapter act on them by
the matrices of the certificate of `scripts/certificates/matter_models.py`, checked by the kernel
(`Ch12/ModelsCheck.lean`, `Ch12/ModelsCheck2.lean`, `Ch12/ModelsSymmetry.lean`,
`Ch12/ModelsBlock.lean`). A spectrum holds in every order of the modes, by the order change of
`Ch12/OrderChange.lean`. Theorem 12.2 is stated in `Ch12/Statements/Models.lean`; its proof is not
here (see `Ch12/CensusMoments.lean`).
-/

namespace Artform

open scoped Matrix ComplexConjugate

open Module FockCalc ModelsData SpecCert ModelsCheck Edge ModelsGroups

namespace ModelsCheck

/-! ### The singlet and the chain's ground state in the sectors -/

theorem singletVec_masks : singletVec.all (fun p =>
    (decode code p.1).toLeft.card == 3 && (decode code p.1).toRight.card == 3) = true := by
  decide +kernel

theorem singlet_mem_endSector : singlet ∈ endSector (Fin 3) (Fin 2) 3 3 := by
  rw [singlet_eq]
  refine Submodule.smul_mem _ _ (Vec.toFock_mem _ _ (fun t => t.toLeft.card = 3 ∧
    t.toRight.card = 3) (fun _ => Iff.rfl) fun p hp => ?_)
  have h := singletVec_masks
  rw [List.all_eq_true] at h
  simpa only [Bool.and_eq_true, beq_iff_eq] using h p hp

theorem chainGround_mem_span : chainGround ∈ Submodule.span ℂ (Set.range chain) :=
  Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, rfl⟩)

theorem B64_mem_range (j : Fin 64) : B64 j ∈ LinearMap.range Φ64 := by
  rw [Φ64, Fintype.range_linearCombination]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem singlet_mem_Φ64 : singlet ∈ LinearMap.range Φ64 := by
  rw [singlet_eq, singletVec, Vec.toFock_combo]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← B64_lit.2.2.2.2.1, ← B64_lit.2.2.2.2.2.1, ← B64_lit.2.2.2.2.2.2.1,
    ← B64_lit.2.2.2.2.2.2.2.1]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (B64_mem_range _))
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (B64_mem_range _)) (Submodule.add_mem _
      (Submodule.smul_mem _ _ (B64_mem_range _)) (Submodule.smul_mem _ _ (B64_mem_range _)))))

theorem chainGround_mem_Φ64 : chainGround ∈ LinearMap.range Φ64 := by
  rw [chainGround_eq, chainVec, Vec.toFock_combo]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← B64_lit.2.2.2.2.2.2.2.2.2, ← B64_lit.2.2.2.2.2.2.2.2.1, ← B64_lit.2.2.2.1,
    ← B64_lit.2.2.1]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (B64_mem_range _))
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (B64_mem_range _)) (Submodule.add_mem _
      (Submodule.smul_mem _ _ (B64_mem_range _)) (Submodule.smul_mem _ _ (B64_mem_range _)))))

theorem singlet_mem_Φ16 : singlet ∈ LinearMap.range Φ16 := by
  rw [← Z33_cube_eq]
  exact Submodule.mem_inf.mpr ⟨singlet_mem_Φ64, singlet_mem_endSector⟩

theorem range_Φ16_le_Φ36 : LinearMap.range Φ16 ≤ LinearMap.range Φ36 := by
  rw [← Z33_36_eq]
  exact inf_le_left

theorem singlet_mem_Φ36 : singlet ∈ LinearMap.range Φ36 := range_Φ16_le_Φ36 singlet_mem_Φ16

theorem singlet_values :
    Vec.sumAt 12 2709 singletVec = 3 ∧ Vec.sumAt 12 2709 chainVec = 0 ∧
      Vec.sumAt 12 63 singletVec = 0 ∧ Vec.sumAt 12 63 chainVec = 3 := by
  decide +kernel

theorem singlet_at : singlet (decode code 2709) = 1 / 2 ∧ chainGround (decode code 2709) = 0 ∧
    singlet (decode code 63) = 0 ∧ chainGround (decode code 63) = 1 / 2 := by
  rw [singlet_eq, chainGround_eq]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Vec.toFock_apply numbering _ (by norm_num), Vec.toFock_apply numbering _ (by norm_num),
    Vec.toFock_apply numbering _ (by norm_num), Vec.toFock_apply numbering _ (by norm_num),
    singlet_values.1, singlet_values.2.1, singlet_values.2.2.1, singlet_values.2.2.2]
  norm_num

theorem singlet_ne_zero : singlet ≠ 0 := fun h => by
  have := singlet_at.1
  rw [h] at this
  norm_num at this

theorem singlet_chainGround_li : LinearIndependent ℂ ![singlet, chainGround] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrFun hst (decode code 2709)
  have h2 := congrFun hst (decode code 63)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, singlet_at] at h1 h2
  constructor
  · linear_combination 2 * h1
  · linear_combination 2 * h2

/-! ### Eigenspaces spanned by named states -/

theorem eq_span_singleton_of_finrank {A : Submodule ℂ (Finset EM → ℂ)} {v : Finset EM → ℂ}
    (hv : v ∈ A) (hv0 : v ≠ 0) (hA : finrank ℂ ↥A = 1) : A = Submodule.span ℂ {v} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v A).mpr hv)
  rw [finrank_span_singleton hv0, hA]

theorem eq_span_pair_of_finrank {A : Submodule ℂ (Finset EM → ℂ)} {v w : Finset EM → ℂ}
    (hv : v ∈ A) (hw : w ∈ A) (hli : LinearIndependent ℂ ![v, w]) (hA : finrank ℂ ↥A = 2) :
    A = Submodule.span ℂ {v, w} := by
  have hr : Set.range ![v, w] = {v, w} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hv
    · exact hw
  · rw [← hr, finrank_span_eq_card hli, Fintype.card_fin, hA]

open Classical in
theorem sectorMult_book_36_eight {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : zeroFluxValues ρ bookOrd = LinearMap.range Φ36) :
    sectorMult ρ bookOrd (tally bookOrd 0) 8 = 1 := by
  rw [sectorMult_book_36 ρ hρ]
  norm_num

theorem eigen8_36 {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : zeroFluxValues ρ bookOrd = LinearMap.range Φ36) :
    zeroFluxValues ρ bookOrd ⊓ Module.End.eigenspace (Matrix.toLin' (tally bookOrd 0)) 8 =
      Submodule.span ℂ {singlet} := by
  refine eq_span_singleton_of_finrank (Submodule.mem_inf.mpr ⟨?_, ?_⟩) singlet_ne_zero ?_
  · rw [hρ]
    exact singlet_mem_Φ36
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact tally_singlet.2
  · exact sectorMult_book_36_eight ρ hρ

theorem eigen8_control :
    zeroFluxValues cubeTriplet bookOrd ⊓
        Module.End.eigenspace (Matrix.toLin' (tally bookOrd 0)) 8 =
      Submodule.span ℂ {singlet} := by
  refine eq_span_singleton_of_finrank (Submodule.mem_inf.mpr ⟨?_, ?_⟩) singlet_ne_zero ?_
  · rw [zeroFluxValues_cube]
    exact singlet_mem_Φ64
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact tally_singlet.2
  · change sectorMult cubeTriplet bookOrd (tally bookOrd 0) 8 = 1
    rw [sectorMult_book_control cubeTriplet zeroFluxValues_cube]
    norm_num

theorem eigen8_cube :
    zeroFluxValues cubeTriplet bookOrd ⊓
        Module.End.eigenspace (Matrix.toLin' (tally bookOrd 1)) 8 =
      Submodule.span ℂ {singlet, chainGround} := by
  refine eq_span_pair_of_finrank (Submodule.mem_inf.mpr ⟨?_, ?_⟩)
    (Submodule.mem_inf.mpr ⟨?_, ?_⟩) singlet_chainGround_li ?_
  · rw [zeroFluxValues_cube]
    exact singlet_mem_Φ64
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact tally_singlet.1
  · rw [zeroFluxValues_cube]
    exact chainGround_mem_Φ64
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact tally_chainGround
  · change sectorMult cubeTriplet bookOrd (tally bookOrd 1) 8 = 2
    rw [sectorMult_book_one cubeTriplet zeroFluxValues_cube]
    norm_num

/-! ### The pairs -/

theorem pair_sector :
    zeroFluxValues cubeTriplet bookOrd ⊓ Fock.numberSector EM 2 =
      Submodule.span ℂ {pairX, pairY} := by
  have hnq : ∀ j : Fin 64, j ∉ ({1, 8} : Finset (Fin 64)) → nq (j / 8) + nq (j % 8) ≠ 2 := by
    decide
  rw [zeroFluxValues_cube, Φ64, range_inf_eq_span B64 B64_linearIndependent _
    (fun t => t.card = 2) (fun _ => Iff.rfl) {1, 8} ?_ ?_]
  · rw [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton,
      ← pairX_eq_B64, ← pairY_eq_B64, Set.pair_comm]
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact B64_mem_numberSector 1
    · exact B64_mem_numberSector 8
  · intro j hj t ht
    exact B64_apply_numberSector j (ht ▸ (hnq j hj).symm)

set_option maxRecDepth 100000 in
theorem pairX_hilbertNorm : Fock.hilbertNorm pairX = Real.sqrt 3 := by
  rw [pairX_eq, Vec.hilbertNorm_eq numbering,
    show (∑ r ∈ Finset.range (2 ^ 12), Vec.sumAt 12 r (basisVec 8) ^ 2 : ℤ) = 3 by
      decide +kernel]
  norm_num

set_option maxRecDepth 100000 in
theorem pairY_hilbertNorm : Fock.hilbertNorm pairY = Real.sqrt 3 := by
  rw [pairY_eq, Vec.hilbertNorm_eq numbering,
    show (∑ r ∈ Finset.range (2 ^ 12), Vec.sumAt 12 r (basisVec 1) ^ 2 : ℤ) = 3 by
      decide +kernel]
  norm_num

end ModelsCheck

/-! ## The book's statements -/

/-- **Proposition 12.1** (the eight invariants of a vertex with two slots). -/
@[book "prop:mm-two-slot-invariants"]
theorem mmTwoSlotInvariants : Statement.mmTwoSlotInvariants := by
  intro ord
  have hne : ∀ i, Vertex.eight ord i ≠ 0 := fun i => (Vertex.eight_linearIndependent ord).ne_zero i
  have hmove : ∀ i, Vertex.omegaEig i ≠ 1 →
      Fock.vertexGamma ord Vertex.omegaOne *ᵥ Vertex.eight ord i ≠ Vertex.eight ord i := by
    intro i hi h
    rw [Vertex.gamma_omega] at h
    have h2 : (Vertex.omegaEig i - 1) • Vertex.eight ord i = 0 := by
      rw [sub_smul, h, one_smul, sub_self]
    exact hne i ((smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hi))
  refine ⟨Vertex.cube_census ord, Vertex.cube_finrank ord, Vertex.eight_linearIndependent ord,
    Vertex.cube_span ord, fun g hg i => Vertex.gamma_six ord hg i,
    ⟨Vertex.omegaOne, Vertex.omegaOne_mem, hmove 1 Vertex.omega_sq_ne_one⟩,
    ⟨Vertex.omegaOne, Vertex.omegaOne_mem, hmove 6 Vertex.omega_ne_one⟩⟩

/-- **Proposition 12.3** (the pair is bound more tightly than the quartet). -/
@[book "prop:mm-diquark"]
theorem mmDiquark : Statement.mmDiquark := by
  have hX : Fock.normalized pairX = ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ • pairX := by
    rw [Fock.normalized, pairX_hilbertNorm]
  have hY : Fock.normalized pairY = ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ • pairY := by
    rw [Fock.normalized, pairY_hilbertNorm]
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨pair_sector, by rw [pairX_hilbertNorm, h3], by rw [pairY_hilbertNorm, h3], ?_, ?_, ?_,
    ?_, ?_, ?_, fun m => ⟨(tally_quartetX m).1, (tally_quartetY m).1⟩⟩
  · rw [hX, hY, Matrix.mulVec_smul, tally_one_pairX, smul_add, smul_comm, smul_comm _ (2 : ℂ)]
  · rw [hX, hY, Matrix.mulVec_smul, tally_one_pairY, smul_add, smul_comm, smul_comm _ (2 : ℂ)]
  · rw [Matrix.mulVec_add, tally_one_pairX, tally_one_pairY]
    module
  · rw [Matrix.mulVec_sub, tally_one_pairX, tally_one_pairY, sub_self]
  · rw [hX, Matrix.mulVec_smul, tally_zero_pairX, smul_comm]
  · rw [hY, Matrix.mulVec_smul, tally_zero_pairY, smul_comm]

/-- **Theorem 12.4** (the spectrum of the tally on one edge). -/
@[book "thm:mm-spectra"]
theorem mmSpectra : Statement.mmSpectra := by
  unfold Statement.mmSpectra
  dsimp only
  refine ⟨fun ord => ⟨finrank_zeroFluxValues_36 _ zeroFluxValues_c3a5 ord,
    finrank_zeroFluxValues_36 _ zeroFluxValues_valentiner ord,
    finrank_zeroFluxValues_36 _ zeroFluxValues_su3 ord,
    finrank_zeroFluxValues_64 _ zeroFluxValues_cube ord, fun μ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩,
    singlet_mem_endSector, chainGround_mem_span, eigen8_36 _ zeroFluxValues_c3a5,
    eigen8_36 _ zeroFluxValues_valentiner, eigen8_36 _ zeroFluxValues_su3, eigen8_cube⟩
  · rw [sectorMult_tally, sectorMult_book_36 _ zeroFluxValues_c3a5]
  · rw [sectorMult_tally, sectorMult_book_36 _ zeroFluxValues_valentiner]
  · rw [sectorMult_tally, sectorMult_book_36 _ zeroFluxValues_su3]
  · rw [sectorMult_tally, sectorMult_book_one _ zeroFluxValues_cube]
  · rw [sectorMult_tally, sectorMult_book_control _ zeroFluxValues_cube]

/-- **Proposition 12.5** (the two-baryon states are ordered by spin). -/
@[book "prop:mm-spin-order"]
theorem mmSpinOrder : Statement.mmSpinOrder := by
  refine ⟨?_, linearIndependent_prod_quartet, fun ord => ?_⟩
  · rw [Z33_cube, range_Φ16, range_prod_quartet]
  · dsimp only
    refine ⟨ladder_ord _ Z33_cube 1 block3_lc ord, ladder_ord _ Z33_ico 1 block3_lc ord,
      ladder_ord _ Z33_c3a5 0 block3_lc0 ord, ladder_ord _ Z33_valentiner 0 block3_lc0 ord,
      ladder_ord _ Z33_su3 0 block3_lc0 ord, ?_, ?_, ?_, ?_, tally_one_eq_zero_Z33 ord⟩
    · rw [Z33_change icoTriplet ord, Z33_change cubeTriplet ord, Z33_ico, Z33_cube]
    · rw [Z33_change c3a5Triplet ord, Z33_change cubeTriplet ord, Z33_c3a5, Z33_cube]
    · rw [Z33_change valentinerTriplet ord, Z33_change cubeTriplet ord, Z33_valentiner,
        Z33_cube]
    · rw [Z33_change su3Triplet ord, Z33_change cubeTriplet ord, Z33_su3, Z33_cube]

/-- **Proposition 12.6** (the pair hop is the cause). -/
@[book "prop:mm-control"]
theorem mmControl : Statement.mmControl := by
  refine ⟨fun ord => ?_, eigen8_control, singlet_mem_endSector, spinSq_singlet, ?_, ?_,
    fun m => ⟨(tally_quartetX m).2, (tally_quartetY m).2⟩, tally_zero_chain, ?_⟩
  · rw [sectorMult_tally, sectorMult_book_control _ zeroFluxValues_cube]
    norm_num
  · rw [tally_zero_pairX]
  · rw [tally_zero_pairY]
  · intro ord μ hμ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ
    simp only [sectorMult_tally, sectorMult_book_control _ zeroFluxValues_cube,
      sectorMult_book_one _ zeroFluxValues_cube, sectorMult_book_one _ zeroFluxValues_ico,
      sectorMult_book_36 _ zeroFluxValues_c3a5, sectorMult_book_36 _ zeroFluxValues_valentiner,
      sectorMult_book_36 _ zeroFluxValues_su3]
    rcases hμ with rfl | rfl | rfl <;> norm_num

/-- **Proposition 12.7** (a symmetry that only a real triplet has). -/
@[book "prop:mm-particle-hole"]
theorem mmParticleHole : Statement.mmParticleHole := by
  refine ⟨fun v hv => ⟨hole_keeps v hv, hole_tally_comm v hv, parity_tally_comm v hv,
    hole_parity_anticomm v hv⟩, fun ord μ => ?_, holeMap_singlet, holeMap_chainGround,
    parityX_singlet, parityX_chainGround, ⟨pairY, pairY_mem_cube, hole_tally0_ne⟩⟩
  rw [sectorMult_tally, sectorMult_book_one _ zeroFluxValues_cube]
  split_ifs <;> decide

/-- **Proposition 12.10** (Models I and II share their zero-flux sector). -/
@[book "prop:mm-same-sector"]
theorem mmSameSector : Statement.mmSameSector := by
  refine ⟨fun ord => ⟨Vertex.eight_linearIndependent ord, Vertex.ico_span ord⟩, fun ord => ?_⟩
  refine ⟨zeroFluxValues_eq_of_book _ _ (zeroFluxValues_ico.trans zeroFluxValues_cube.symm) ord,
    finrank_zeroFluxValues_64 _ zeroFluxValues_ico ord, fun P hP1 hP2 hP3 =>
      pvvp_eq_tally icoTriplet Vertex.icoTriplet_mem ico_irreducible ord 1
        (Or.inl ⟨rfl, ico_real⟩) P hP1 hP2 hP3,
    fun P hP1 hP2 hP3 =>
      pvvp_eq_tally cubeTriplet cubeTriplet_mem CubeGroup.isIrreducible_tripletRep ord 1
        (Or.inl ⟨rfl, cubeTriplet_real⟩) P hP1 hP2 hP3, fun μ => ⟨?_, ?_⟩⟩
  · rw [sectorMult_tally icoTriplet ord, sectorMult_tally cubeTriplet ord,
      sectorMult_book_one _ zeroFluxValues_ico, sectorMult_book_one _ zeroFluxValues_cube]
  · rw [sectorMult_tally, sectorMult_book_one _ zeroFluxValues_ico]

/-- **Proposition 12.12** (triality, and the pair moment). -/
@[book "prop:mm-centre"]
theorem mmCentre : Statement.mmCentre := by
  refine ⟨fun S _ _ ord n hn => census_eq_zero_of_centre c3a5Triplet ord
      ⟨(Multiplicative.ofAdd 1, 1), Vertex.c3a5Triplet_omega⟩ hn,
    c3a5_pair_moment, c3a5_no_pair_invariant,
    fun ord P hP1 hP2 hP3 => pvvp_eq_tally c3a5Triplet Vertex.c3a5Triplet_mem c3a5_irreducible
      ord 0 (Or.inr ⟨rfl, c3a5_no_pair_invariant⟩) P hP1 hP2 hP3,
    fun ord => ⟨Vertex.six_linearIndependent ord, Vertex.c3a5_span ord⟩, fun ord => ⟨?_, ?_⟩⟩
  · exact zeroFluxValues_eq_of_book _ _ (zeroFluxValues_c3a5.trans zeroFluxValues_su3.symm) ord
  · intro μ
    rw [sectorMult_tally, sectorMult_book_36 _ zeroFluxValues_c3a5]

/-! ## Non-vacuity -/

/-- Proposition 12.1 in the book's order: eight invariants, and the pair is moved by `ω 1`. -/
example : finrank ℂ ↥(Edge.vertexInvariants cubeTriplet Vertex.bookOrd) = 8 ∧
    Fock.vertexGamma Vertex.bookOrd Vertex.omegaOne *ᵥ Vertex.pair Vertex.bookOrd ≠
      Vertex.pair Vertex.bookOrd := by
  refine ⟨(mmTwoSlotInvariants Vertex.bookOrd).2.1, ?_⟩
  have hne := (Vertex.eight_linearIndependent Vertex.bookOrd).ne_zero 1
  intro h
  rw [show Vertex.pair Vertex.bookOrd = Vertex.eight Vertex.bookOrd 1 from rfl,
    Vertex.gamma_omega] at h
  have h2 : (Vertex.omegaEig 1 - 1) • Vertex.eight Vertex.bookOrd 1 = 0 := by
    rw [sub_smul, h, one_smul, sub_self]
  exact hne ((smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr Vertex.omega_sq_ne_one))

theorem pair_values : Vec.sumAt 12 3 (basisVec 8) = 1 ∧ Vec.sumAt 12 3 (basisVec 1) = 0 := by
  decide +kernel

/-- Proposition 12.3: the bonding pair `D_x + D_y` is a nonzero state with the value `4`. -/
example : Edge.pairX + Edge.pairY ≠ 0 ∧
    Edge.tally Edge.bookOrd 1 *ᵥ (Edge.pairX + Edge.pairY) =
      (4 : ℂ) • (Edge.pairX + Edge.pairY) := by
  refine ⟨fun h => ?_, mmDiquark.2.2.2.2.2.1⟩
  have h3 := congrFun h (decode code 3)
  rw [Pi.add_apply, pairX_eq, pairY_eq, Vec.toFock_apply numbering _ (by norm_num),
    Vec.toFock_apply numbering _ (by norm_num), pair_values.1, pair_values.2] at h3
  norm_num at h3

/-- Theorem 12.4: the ground value `8` of Model I is reached, by the singlet. -/
example : Edge.singlet ∈ Edge.zeroFluxValues cubeTriplet Edge.bookOrd ⊓
    Module.End.eigenspace (Matrix.toLin' (Edge.tally Edge.bookOrd 1)) 8 ∧ Edge.singlet ≠ 0 := by
  refine ⟨?_, singlet_ne_zero⟩
  rw [mmSpectra.2.2.2.2.2.2]
  exact Submodule.subset_span (Set.mem_insert _ _)

/-- Proposition 12.5 in the book's order, for Model I: one state of spin `0`, at `8`. -/
example : finrank ℂ ↥((Edge.zeroFluxValues cubeTriplet Edge.bookOrd ⊓
    Edge.endSector (Fin 3) (Fin 2) 3 3) ⊓
      Module.End.eigenspace (Matrix.toLin' (Edge.spinSq Edge.bookOrd)) 0) = 1 :=
  (ladder_ord _ Z33_cube 1 block3_lc Edge.bookOrd).2.2.2.2.2.2.2.2.2.1

/-- Proposition 12.6: the control reaches `8` once, on a nonzero state. -/
example : Edge.sectorMult cubeTriplet Edge.bookOrd (Edge.tally Edge.bookOrd 0) 8 = 1 :=
  mmControl.1 Edge.bookOrd

/-- Proposition 12.7: the hole map moves the singlet, a nonzero state, to the chain. -/
example : Edge.holeMap Edge.bookOrd *ᵥ Edge.singlet = Edge.chainGround ∧ Edge.singlet ≠ 0 :=
  ⟨mmParticleHole.2.2.1, singlet_ne_zero⟩

/-- Proposition 12.10: the hypotheses on `P` are met, by the average over the link and the gauge
pairs (`ThereAndBack.zeroFluxProj`), for the icosahedral group. -/
example (ψ : icoGroup → Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ)
    (hψ : ψ ∈ Edge.zeroFlux icoTriplet Edge.bookOrd) :
    ThereAndBack.zeroFluxProj icoTriplet Edge.bookOrd
        (Edge.hop icoTriplet Edge.bookOrd (Edge.hop icoTriplet Edge.bookOrd ψ)) =
      Edge.atEachLink (Edge.tally Edge.bookOrd 1) ψ :=
  (mmSameSector.2 Edge.bookOrd).2.2.1 _ (ThereAndBack.zeroFluxProj_mem _ _)
    (fun _ h => ThereAndBack.zeroFluxProj_fix _ _ h)
    (ThereAndBack.zeroFluxProj_adj (fun g => Vertex.mem_unitary (Vertex.icoTriplet_mem g)) _)
    ψ hψ

/-- Proposition 12.12: the hypotheses on `P` are met for `C₃ × A₅`, and the census vanishes at
one quark on an edge with two slots. -/
example (ψ : C3A5 → Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ)
    (hψ : ψ ∈ Edge.zeroFlux c3a5Triplet Edge.bookOrd) :
    ThereAndBack.zeroFluxProj c3a5Triplet Edge.bookOrd
        (Edge.hop c3a5Triplet Edge.bookOrd (Edge.hop c3a5Triplet Edge.bookOrd ψ)) =
      Edge.atEachLink (Edge.tally Edge.bookOrd 0) ψ ∧
    finrank ℂ ↥(Edge.colourless c3a5Triplet Edge.bookOrd ⊓
      Edge.stateSector C3A5 (Fock.numberSector (Edge.Mode (Fin 3) (Fin 2)) 1)) = 0 :=
  ⟨mmCentre.2.2.2.1 Edge.bookOrd _ (ThereAndBack.zeroFluxProj_mem _ _)
    (fun _ h => ThereAndBack.zeroFluxProj_fix _ _ h)
    (ThereAndBack.zeroFluxProj_adj (fun g => Vertex.mem_unitary (Vertex.c3a5Triplet_mem g)) _)
    ψ hψ, mmCentre.1 (Fin 2) Edge.bookOrd 1 (by norm_num)⟩

end Artform
