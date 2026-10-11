import ArtformTextbook.Ch13.Statements.ThirdOrder
import ArtformTextbook.Ch13.TransferMoments

/-!
# The third-order transfer (Theorem 13.8)

* **Two resolvents.** For a zero-flux state `ψ` the hop `V ψ` lies in the triplet blocks, at the
  level `E₃` (`ThereAndBack.electricEnergy_hop`), so the first resolvent acts as the number
  `-1/(κ E₃)`. For the second, `P V` sees only those blocks: `V`, the electric energy of any table
  and `P` are self-adjoint, and `H_F V P = F₃ V P` for a table `F` that declares `F₃` on the
  triplet and its conjugate, so `P V H_F = F₃ P V` (`ThirdOrder.proj_hop_electricEnergy`). With
  `F = 1/E` the second resolvent also acts as `-1/(κ E₃)`, and
  `P V R V R V P = P V³ P/(κ E₃)²`.
* **The words.** `P V³ P` acts on the zero-flux sector as the words
  (`TransferMoments.transferVal_eq`), from the cubic moment of Proposition 11.19.
* **`P V P = 0`** is the first part of Theorem 11.20; for a complex triplet its hypothesis, that
  `3 ⊗ 3` has no invariant, follows from the centre: `ω 1` multiplies an invariant by `ω² ≠ 1`.
-/

namespace Artform

open scoped Matrix ComplexConjugate

open Module Edge ThereAndBack TransferMoments

namespace ThirdOrder

variable {G : Type} [Group G] [Fintype G] {S : Type} [Fintype S] [DecidableEq S]
  {ι : Type} [Fintype ι] {d : ι → ℕ}

omit [Fintype G] in
theorem hop_smul (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (ord : LinearOrder (Mode (Fin 3) S))
    (c : ℂ) (ψ : G → Finset (Mode (Fin 3) S) → ℂ) : hop ρ ord (c • ψ) = c • hop ρ ord ψ := by
  funext U
  simp only [hop, Pi.smul_apply, Matrix.mulVec_smul]

omit [Fintype S] [DecidableEq S] in
theorem electricEnergy_smul (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (E : ι → ℚ) (c : ℂ)
    (ψ : G → Finset (Mode (Fin 3) S) → ℂ) :
    electricEnergy σ E (c • ψ) = c • electricEnergy σ E ψ := by
  simp only [electricEnergy, tableConv, Finset.smul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  have e : leftWrite h (c • ψ) = c • leftWrite h ψ := rfl
  rw [e, smul_comm]

omit [DecidableEq S] in
/-- The electric energy of any table is self-adjoint. -/
theorem statePairing_electricEnergy (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (E : ι → ℚ)
    (ψ φ : G → Finset (Mode (Fin 3) S) → ℂ) :
    statePairing (electricEnergy σ E ψ) φ = statePairing ψ (electricEnergy σ E φ) := by
  unfold electricEnergy
  exact statePairing_tableConv_adj (convolution_energy_conjTranspose σ E) ψ φ

/-- `P V` sees only the triplet blocks: `P V H_F = F₃ P V` for a table `F` that declares `F₃` on
the triplet and its conjugate. -/
theorem proj_hop_electricEnergy {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (hirr : (tripletRep ρ).IsIrreducible) {ord : LinearOrder (Mode (Fin 3) S)}
    {σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)} (hσ : IsCompleteFamily σ) (F : ι → ℚ)
    (F₃ : ℚ) (hF : ∀ i, (Nonempty ((tripletRep ρ).Equiv (σ i)) ∨
      Nonempty ((conjTripletRep ρ).Equiv (σ i))) → F i = F₃)
    {P : (G → Finset (Mode (Fin 3) S) → ℂ) →ₗ[ℂ] (G → Finset (Mode (Fin 3) S) → ℂ)}
    (hP : IsZeroFluxProj ρ ord P) (Y : G → Finset (Mode (Fin 3) S) → ℂ) :
    P (hop ρ ord (electricEnergy σ F Y)) = ((F₃ : ℚ) : ℂ) • P (hop ρ ord Y) := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  refine proj_eq_of_orth hP1 hP2 hP3 ((zeroFlux ρ ord).smul_mem _ (hP1 _)) fun ξ hξ => ?_
  rw [← statePairing_hop_adj, ← statePairing_electricEnergy,
    electricEnergy_hop hirr ord hσ F F₃ hF hξ, statePairing_smul_left, statePairing_hop_adj,
    statePairing_smul_right, ← hP3, hP2 ξ hξ, map_ratCast]

/-- The third-order term is `P V³ P/(κ E₃)²`: both resolvents act as `-1/(κ E₃)`. -/
theorem thirdOrder_eq {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ} (hirr : (tripletRep ρ).IsIrreducible)
    {ord : LinearOrder (Mode (Fin 3) S)} {σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)}
    (hσ : IsCompleteFamily σ) {E : ι → ℚ} (E₃ : ℚ)
    (hE₃ : ∀ i, (Nonempty ((tripletRep ρ).Equiv (σ i)) ∨
      Nonempty ((conjTripletRep ρ).Equiv (σ i))) → E i = E₃) (κ : ℝ)
    {P : (G → Finset (Mode (Fin 3) S) → ℂ) →ₗ[ℂ] (G → Finset (Mode (Fin 3) S) → ℂ)}
    (hP : IsZeroFluxProj ρ ord P) {ψ : G → Finset (Mode (Fin 3) S) → ℂ}
    (hψ : ψ ∈ zeroFlux ρ ord) :
    thirdOrder ρ ord σ E κ P ψ =
      (((κ * E₃ : ℝ) : ℂ) ^ 2)⁻¹ • P (hop ρ ord (hop ρ ord (hop ρ ord (P ψ)))) := by
  have hinv : ∀ i, (Nonempty ((tripletRep ρ).Equiv (σ i)) ∨
      Nonempty ((conjTripletRep ρ).Equiv (σ i))) → (fun i => (E i)⁻¹) i = E₃⁻¹ :=
    fun i hi => by simp only [hE₃ i hi]
  have hPψ : P ψ = ψ := hP.2.1 ψ hψ
  have h1 : electricEnergy σ (fun i => (E i)⁻¹) (hop ρ ord ψ) =
      ((E₃⁻¹ : ℚ) : ℂ) • hop ρ ord ψ :=
    electricEnergy_hop hirr ord hσ _ _ hinv hψ
  have h2 := proj_hop_electricEnergy hirr hσ (fun i => (E i)⁻¹) E₃⁻¹ hinv hP
    (hop ρ ord (hop ρ ord ψ))
  simp only [thirdOrder, reducedResolvent, hPψ, h1, hop_smul, electricEnergy_smul, map_smul, h2,
    smul_smul]
  congr 1
  push_cast
  ring

/-- `P V³ P` acts on the zero-flux sector as the words of Theorem 13.8. -/
theorem proj_hop3_eq_words {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (hirr : (tripletRep ρ).IsIrreducible)
    (h1 : finrank ℂ ↥(tripleInvariants ρ) = 1) (ord : LinearOrder (Mode (Fin 3) S)) (real : Bool)
    (hreal : real = true → ∀ U i j, conj (ρ U i j) = ρ U i j)
    (hcentre : real = false → ∃ h₀, ρ h₀ = Exact.omega • 1)
    {P : (G → Finset (Mode (Fin 3) S) → ℂ) →ₗ[ℂ] (G → Finset (Mode (Fin 3) S) → ℂ)}
    (hP : IsZeroFluxProj ρ ord P) {ψ : G → Finset (Mode (Fin 3) S) → ℂ}
    (hψ : ψ ∈ zeroFlux ρ ord) :
    P (hop ρ ord (hop ρ ord (hop ρ ord (P ψ)))) = atEachLink (transferWords ord real) ψ := by
  have hv : ψ 1 ∈ zeroFluxValues ρ ord :=
    (mem_zeroFluxValues ρ ord _).mpr ((mem_zeroFlux_iff ρ ord ψ).mp hψ).2
  have key := transferVal_eq ρ hρ ord real (third_moment ρ hρ hirr h1) hreal hcentre P hP (ψ 1) hv
  have hconst := const_of_mem_zeroFlux hψ
  have e : P (hop ρ ord (hop ρ ord (hop ρ ord (P ψ)))) 1 = transferVal ρ ord P (ψ 1) := by
    simp only [transferVal, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← hconst]
  rw [const_of_mem_zeroFlux (hP.1 (hop ρ ord (hop ρ ord (hop ρ ord (P ψ)))))]
  funext U
  simp only [atEachLink]
  rw [e, key, congrFun hconst U, transferWords]

omit [Fintype G] in
/-- A central element acting by `ω` leaves `3 ⊗ 3` no invariant. -/
theorem no_pair_invariant {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ} {h₀ : G}
    (hh₀ : ρ h₀ = Exact.omega • 1) (T : Matrix (Fin 3) (Fin 3) ℂ)
    (hT : ∀ U, ρ U * T * (ρ U)ᵀ = T) : T = 0 := by
  have h := hT h₀
  rw [hh₀, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, ← sq] at h
  have h2 : (Exact.omega ^ 2 - 1) • T = 0 := by rw [sub_smul, h, one_smul, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr Vertex.omega_sq_ne_one)

theorem claims_of {G : Type} [Group G] [Fintype G] {S : Type} [Fintype S] [DecidableEq S]
    {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ} (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (hirr : (tripletRep ρ).IsIrreducible) (h1 : finrank ℂ ↥(tripleInvariants ρ) = 1)
    {real : Bool} (hr : (real = true ∧ ∀ U i j, conj (ρ U i j) = ρ U i j) ∨
      (real = false ∧ ∃ h₀, ρ h₀ = Exact.omega • 1))
    (ord : LinearOrder (Mode (Fin 3) S)) (ι : Type) [Fintype ι] (d : ι → ℕ)
    (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (hσ : IsCompleteFamily σ) (E : ι → ℚ)
    (hE : IsEnergyTable σ E) (E₃ : ℚ)
    (hE₃ : ∀ i, (Nonempty ((tripletRep ρ).Equiv (σ i)) ∨
      Nonempty ((conjTripletRep ρ).Equiv (σ i))) → E i = E₃) (κ : ℝ) (hκ : 0 < κ)
    (P : (G → Finset (Mode (Fin 3) S) → ℂ) →ₗ[ℂ] (G → Finset (Mode (Fin 3) S) → ℂ))
    (hP : IsZeroFluxProj ρ ord P) :
    (∀ ψ, P (hop ρ ord (P ψ)) = 0) ∧
    ∀ ψ ∈ zeroFlux ρ ord,
      thirdOrder ρ ord σ E κ P ψ =
        (((κ * E₃ : ℝ) : ℂ) ^ 2)⁻¹ • P (hop ρ ord (hop ρ ord (hop ρ ord (P ψ)))) ∧
      P (hop ρ ord (hop ρ ord (hop ρ ord (P ψ)))) = atEachLink (transferWords ord real) ψ := by
  have hPV : ∀ ψ, P (hop ρ ord (P ψ)) = 0 := by
    rcases hr with ⟨_, hre⟩ | ⟨_, h₀, hh₀⟩
    · exact (Artform.mtThereAndBack G S ρ hρ hirr ord ι d σ hσ E hE E₃ hE₃ κ hκ 1
        (Or.inl ⟨rfl, hre⟩) P hP.1 hP.2.1 hP.2.2).1
    · exact (Artform.mtThereAndBack G S ρ hρ hirr ord ι d σ hσ E hE E₃ hE₃ κ hκ 0
        (Or.inr ⟨rfl, no_pair_invariant hh₀⟩) P hP.1 hP.2.1 hP.2.2).1
  refine ⟨hPV, fun ψ hψ => ⟨thirdOrder_eq hirr hσ E₃ hE₃ κ hP hψ, ?_⟩⟩
  rcases hr with ⟨rfl, hre⟩ | ⟨rfl, hc⟩
  · exact proj_hop3_eq_words hρ hirr h1 ord true (fun _ => hre) (fun h => absurd h (by decide))
      hP hψ
  · exact proj_hop3_eq_words hρ hirr h1 ord false (fun h => absurd h (by decide)) (fun _ => hc)
      hP hψ

end ThirdOrder

open ThirdOrder in
/-- **Theorem 13.8** (the third-order transfer). On the zero-flux sector of one edge, the
third-order term of the energy law is `H⁽³⁾ = L/(κ E₃)²`, `L = P V³ P`, and with the cubic moment
of Proposition 11.19, `L` is the words: `(1/6) Σ sgn(c) sgn(c') A A A + h.c.` for a complex
triplet, and the eight words in `A` and `A†` with the same weight for a real one. -/
@[book "thm:ml-transfer"]
theorem mlTransfer : Statement.mlTransfer := by
  dsimp only [Statement.mlTransfer]
  refine ⟨fun G _ _ S _ _ ρ hρ hirr h1 real hr ord ι _ d σ hσ E hE E₃ hE₃ κ hκ P hP =>
    claims_of hρ hirr h1 hr ord ι d σ hσ E hE E₃ hE₃ κ hκ P hP, fun S _ _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact fun ord ι _ d σ hσ E hE E₃ hE₃ κ hκ P hP =>
      claims_of cubeTriplet_mem CubeGroup.isIrreducible_tripletRep finrank_tripleInvariants_cube
        (Or.inl ⟨rfl, cubeTriplet_real⟩) ord ι d σ hσ E hE E₃ hE₃ κ hκ P hP
  · exact fun ord ι _ d σ hσ E hE E₃ hE₃ κ hκ P hP =>
      claims_of Vertex.icoTriplet_mem ModelsGroups.ico_irreducible finrank_tripleInvariants_ico
        (Or.inl ⟨rfl, ModelsGroups.ico_real⟩) ord ι d σ hσ E hE E₃ hE₃ κ hκ P hP
  · exact fun ord ι _ d σ hσ E hE E₃ hE₃ κ hκ P hP =>
      claims_of Vertex.c3a5Triplet_mem ModelsGroups.c3a5_irreducible
        finrank_tripleInvariants_c3a5
        (Or.inr ⟨rfl, (Multiplicative.ofAdd 1, 1), Vertex.c3a5Triplet_omega⟩)
        ord ι d σ hσ E hE E₃ hE₃ κ hκ P hP
  · exact fun ord ι _ d σ hσ E hE E₃ hE₃ κ hκ P hP =>
      claims_of Vertex.valentinerTriplet_mem valentiner_irreducible
        finrank_tripleInvariants_valentiner
        (Or.inr ⟨rfl, Vertex.c3a5ToValentiner (Multiplicative.ofAdd 1, 1), by
          rw [Vertex.valentinerTriplet_c3a5, Vertex.c3a5Triplet_omega]; rfl⟩)
        ord ι d σ hσ E hE E₃ hE₃ κ hκ P hP

/-! ## Non-vacuity -/

open Classical in
/-- The hypotheses of Theorem 13.8 are met on the cube group with two slots: a complete family
(Theorem 11.4), the energy table with the level `4/3` off the trivial member, and the orthogonal
projector onto the zero-flux sector. -/
example : ∃ (n : ℕ) (d : Fin n → ℕ) (σ : ∀ i, Representation ℂ cubeGroup (Fin (d i) → ℂ))
    (E : Fin n → ℚ) (P : (cubeGroup → Finset (Mode (Fin 3) (Fin 2)) → ℂ) →ₗ[ℂ]
      (cubeGroup → Finset (Mode (Fin 3) (Fin 2)) → ℂ)),
    IsCompleteFamily σ ∧ IsEnergyTable σ E ∧
    (∀ i, (Nonempty ((tripletRep cubeTriplet).Equiv (σ i)) ∨
      Nonempty ((conjTripletRep cubeTriplet).Equiv (σ i))) → E i = 4 / 3) ∧
    IsZeroFluxProj cubeTriplet Edge.bookOrd P := by
  obtain ⟨n, d, σ, h1, h2, h3⟩ := (mtBlocks cubeGroup).1
  have hirr := CubeGroup.isIrreducible_tripletRep
  refine ⟨n, d, σ, fun i => if (σ i).IsTrivial then 0 else 4 / 3,
    zeroFluxProj cubeTriplet Edge.bookOrd, ⟨h1, h2, h3⟩,
    fun i => ⟨fun h => by simp [h], fun h => by norm_num [h]⟩, fun i hi => ?_,
    ⟨zeroFluxProj_mem _ _, fun ψ hψ => zeroFluxProj_fix _ _ hψ,
      zeroFluxProj_adj (fun g => (Matrix.mem_specialUnitaryGroup_iff.mp (cubeTriplet_mem g)).1)
        _⟩⟩
  have hnt : ¬ (σ i).IsTrivial := by
    intro ht
    rcases hi with he | he
    · obtain ⟨e⟩ := he
      exact not_isTrivial_tripletRep hirr (isTrivial_of_equiv e ht)
    · obtain ⟨e⟩ := he
      exact not_isTrivial_tripletRep
          (ρ := (RingHom.mapMatrix (starRingEnd ℂ)).toMonoidHom.comp cubeTriplet)
          (conjTripletRep_irreducible hirr) (isTrivial_of_equiv e ht)
  simp [hnt]

end Artform
