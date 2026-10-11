import ArtformTextbook.Ch11.ThereAndBack
import ArtformTextbook.Ch12.VertexInvariants

/-!
# The colour groups of the models: irreducibility, the second return, the centre

* The triplets of Model II and of Refinement I are irreducible: they contain the half-turns about
  the three axes and the cyclic permutation of the axes (`ModelsGroups.isIrreducible_of_turns`).
* For a finite colour group with an irreducible triplet in `SU(3)`, every orthogonal projector
  `P` onto the zero-flux sector gives `P V² P = Ω` there (`ModelsGroups.pvvp_eq_tally`), the
  argument of Theorem 11.20 from the moments of Proposition 11.19.
* A colour group containing `ω 1` has no colourless state whose quark number is not a multiple
  of three (`ModelsGroups.census_eq_zero_of_centre`); for `C₃ × A₅` the pair moment is
  `⟨χ²⟩ = 0` and `3 ⊗ 3` has no invariant.
-/

namespace Artform

open scoped Matrix ComplexConjugate

open Edge ThereAndBack ColourGroups Icosahedron Exact

namespace ModelsGroups

/-! ### Irreducibility -/

/-- The half-turn about the axis `i`: the sign `+1` on the axis and `-1` on the other two. -/
def halfTurn (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun j => if j = i then 1 else -1

/-- A triplet containing the three half-turns about the axes and the cyclic permutation of the
axes is irreducible: the half-turns project a nonzero invariant subspace onto an axis, and the
permutation carries that axis to the other two. -/
theorem isIrreducible_of_turns {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (hh : ∀ i, ∃ g, ρ g = halfTurn i)
    (hp : ∃ g, ∀ v : Fin 3 → ℂ, ρ g *ᵥ v = fun j => v (finRotate 3 j)) :
    (tripletRep ρ).IsIrreducible := by
  have hact : ∀ (g : G) (v : Fin 3 → ℂ), tripletRep ρ g v = ρ g *ᵥ v := fun g v => rfl
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · by_cases hW : ∀ v ∈ W.toSubmodule, v = 0
    · left
      apply Subrepresentation.toSubmodule_injective
      exact (Submodule.eq_bot_iff _).mpr hW
    · right
      push Not at hW
      obtain ⟨v, hv, hv0⟩ := hW
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        push Not at h
        exact hv0 (funext h)
      have hsingle : (Pi.single i 1 : Fin 3 → ℂ) ∈ W.toSubmodule := by
        obtain ⟨g, hg⟩ := hh i
        have h1 := W.apply_mem_toSubmodule g hv
        have e : (Matrix.diagonal fun j => if j = i then (1 : ℂ) else -1) *ᵥ v =
            fun j => if j = i then v j else -v j := by
          funext j
          rw [Matrix.mulVec_diagonal]
          split_ifs <;> ring
        rw [hact, hg, halfTurn, e] at h1
        have h2 := W.toSubmodule.add_mem hv h1
        have h3 := W.toSubmodule.smul_mem ((2 * v i)⁻¹) h2
        convert h3 using 1
        funext j
        simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs with hj
        · subst hj
          field_simp
          ring
        · ring
      obtain ⟨p, hpv⟩ := hp
      have hrot : ∀ j, (Pi.single j 1 : Fin 3 → ℂ) ∈ W.toSubmodule →
          (Pi.single ((finRotate 3).symm j) 1 : Fin 3 → ℂ) ∈ W.toSubmodule := by
        intro j hj
        have := W.apply_mem_toSubmodule p hj
        rw [hact, hpv] at this
        convert this using 1
        funext k
        simp only [Pi.single_apply, Equiv.eq_symm_apply]
      have hall : ∀ j, (Pi.single j 1 : Fin 3 → ℂ) ∈ W.toSubmodule := by
        intro j
        have h1 := hrot _ hsingle
        have h2 := hrot _ h1
        fin_cases i <;> fin_cases j <;> first | exact hsingle | exact h1 | exact h2
      apply Subrepresentation.toSubmodule_injective
      change W.toSubmodule = ⊤
      rw [eq_top_iff]
      intro w _
      have hw : w = ∑ j, w j • (Pi.single j 1 : Fin 3 → ℂ) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hw]
      exact W.toSubmodule.sum_mem fun j _ => W.toSubmodule.smul_mem _ (hall j)

/-! ### Four rotations of the icosahedron -/

theorem gE_16 : gE 16 = m 2 0 0 0 0 0 0 0 (-2) 0 0 0 0 0 0 0 (-2) 0 := by decide

theorem gE_7 : gE 7 = m (-2) 0 0 0 0 0 0 0 2 0 0 0 0 0 0 0 (-2) 0 := by decide

theorem gE_12 : gE 12 = m (-2) 0 0 0 0 0 0 0 (-2) 0 0 0 0 0 0 0 2 0 := by decide

theorem gE_40 : gE 40 = m 0 0 2 0 0 0 0 0 0 0 2 0 2 0 0 0 0 0 := by decide

theorem rotC_16 : rotC 16 = halfTurn 0 := by
  rw [rotC, R, gE_16]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M3.toRealHalf, m, v, ZPhi.toReal, halfTurn]

theorem rotC_7 : rotC 7 = halfTurn 1 := by
  rw [rotC, R, gE_7]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M3.toRealHalf, m, v, ZPhi.toReal, halfTurn]

theorem rotC_12 : rotC 12 = halfTurn 2 := by
  rw [rotC, R, gE_12]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M3.toRealHalf, m, v, ZPhi.toReal, halfTurn]

theorem rotC_40_mulVec (w : Fin 3 → ℂ) : rotC 40 *ᵥ w = fun j => w (finRotate 3 j) := by
  rw [rotC, R, gE_40]
  funext j
  fin_cases j <;>
    simp [M3.toRealHalf, m, v, ZPhi.toReal, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      finRotate_apply]

theorem icoTriplet_icoElt (k : Fin 60) : icoTriplet (icoElt k) = rotC k := rfl

theorem ico_halfTurns (i : Fin 3) : ∃ g, icoTriplet g = halfTurn i := by
  fin_cases i
  · exact ⟨icoElt 16, rotC_16⟩
  · exact ⟨icoElt 7, rotC_7⟩
  · exact ⟨icoElt 12, rotC_12⟩

/-- The triplet of Model II is irreducible. -/
theorem ico_irreducible : (tripletRep icoTriplet).IsIrreducible :=
  isIrreducible_of_turns icoTriplet ico_halfTurns ⟨icoElt 40, rotC_40_mulVec⟩

/-- The triplet of Refinement I is irreducible. -/
theorem c3a5_irreducible : (tripletRep c3a5Triplet).IsIrreducible :=
  isIrreducible_of_turns c3a5Triplet
    (fun i => by
      obtain ⟨g, hg⟩ := ico_halfTurns i
      exact ⟨(1, g), by rw [Vertex.c3a5Triplet_ico, hg]⟩)
    ⟨(1, icoElt 40), fun w => by rw [Vertex.c3a5Triplet_ico, icoTriplet_icoElt, rotC_40_mulVec]⟩

/-- The triplet of Model II is real. -/
theorem ico_real (U : icoGroup) (i j : Fin 3) : conj (icoTriplet U i j) = icoTriplet U i j := by
  obtain ⟨R', _, hg⟩ := U.2
  change conj (((U : Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i j) =
    ((U : Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i j
  rw [hg, Matrix.map_apply, Complex.conj_ofReal]

/-! ### The centre -/

theorem omega_pow_ne_one {n : ℕ} (hn : ¬ 3 ∣ n) : Exact.omega ^ n ≠ 1 := by
  rw [← Exact.omega_pow_mod]
  have h : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h
  · rw [h, pow_one]
    exact Vertex.omega_ne_one
  · rw [h]
    exact Vertex.omega_sq_ne_one

/-- For `C₃ × A₅`, `3 ⊗ 3` has no invariant: `ω 1` multiplies it by `ω² ≠ 1`. -/
theorem c3a5_no_pair_invariant (T : Matrix (Fin 3) (Fin 3) ℂ)
    (hT : ∀ U, c3a5Triplet U * T * (c3a5Triplet U)ᵀ = T) : T = 0 := by
  have h := hT (Multiplicative.ofAdd 1, 1)
  rw [Vertex.c3a5Triplet_omega, Vertex.omegaOne, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← sq] at h
  have h2 : (Exact.omega ^ 2 - 1) • T = 0 := by rw [sub_smul, h, one_smul, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr Vertex.omega_sq_ne_one)

/-- The pair moment of `C₃ × A₅`: `⟨χ²⟩ = 0`. -/
theorem c3a5_pair_moment : groupAvg C3A5 (fun x => C3A5.char x ^ 2) = 0 := by
  have h3 : ∑ j : Multiplicative (ZMod 3), (Exact.omega ^ (Multiplicative.toAdd j).val) ^ 2 =
      0 := by
    rw [Fintype.sum_equiv Multiplicative.toAdd _
      (fun j : ZMod 3 => (Exact.omega ^ j.val) ^ 2) (fun _ => rfl)]
    change ∑ j : Fin 3, (Exact.omega ^ (j : ℕ)) ^ 2 = 0
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_pow, pow_one]
    linear_combination Exact.omega_sq_add + Exact.omega * Exact.omega_pow_three
  rw [groupAvg, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
  simp only [char_C3A5, mul_pow]
  rw [← Finset.sum_mul_sum, h3, zero_mul, mul_zero]

/-- `Γ(c 1)` multiplies the table of `n` occupied modes by `c^{|n|}`. -/
theorem secondQuant_smul_one_ket {M : Type*} [Fintype M] [DecidableEq M] (ord : LinearOrder M)
    (c : ℂ) (n : Finset M) :
    Fock.secondQuant ord (c • 1) *ᵥ Fock.ket n = c ^ n.card • Fock.ket n := by
  have htc : ∀ a, Fock.transformedCreation ord (c • 1) a = c • Fock.creation ord a := by
    intro a
    rw [Fock.transformedCreation, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have htr : ∀ L : List M, Fock.trProd ord (c • 1) L = c ^ L.length • Fock.crProd ord L := by
    intro L
    induction L with
    | nil => simp [Fock.trProd, Fock.crProd]
    | cons a L ih =>
      simp only [Fock.trProd, Fock.crProd, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih, htc, smul_mul_smul_comm, List.length_cons, pow_succ, mul_comm]
  rw [Fock.secondQuant_mulVec_ket, htr, Matrix.smul_mulVec, Fock.crProd_sort_mulVec_vacuum,
    Finset.length_sort]

theorem diag_smul_one {C S : Type*} [DecidableEq C] [DecidableEq S]
    (c : ℂ) : (diag (c • (1 : Matrix C C ℂ)) (c • 1) : Matrix (Mode C S) (Mode C S) ℂ) =
      c • 1 := by
  ext (⟨c₁, s₁⟩ | ⟨c₁, s₁⟩) (⟨c₂, s₂⟩ | ⟨c₂, s₂⟩) <;>
    simp [diag, Matrix.one_apply, ite_and] <;> split_ifs <;> rfl

theorem eq_sum_ket {M : Type*} [Fintype M] [DecidableEq M] (u : Finset M → ℂ) :
    u = ∑ n, u n • Fock.ket n := by
  funext t
  simp [Fock.ket, Finset.sum_apply, Pi.single_apply]

/-- A colour group whose triplet contains `ω 1` has no colourless state of one edge whose quark
number is not a multiple of three. -/
theorem census_eq_zero_of_centre {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    {S : Type*} [Fintype S] [DecidableEq S] (ord : LinearOrder (Mode (Fin 3) S))
    (hω : ∃ h, ρ h = Exact.omega • 1) {n : ℕ} (hn : ¬ 3 ∣ n) :
    Module.finrank ℂ ↥(colourless ρ ord ⊓
      stateSector G (Fock.numberSector (Mode (Fin 3) S) n)) = 0 := by
  obtain ⟨h₀, hh₀⟩ := hω
  suffices hbot : colourless ρ ord ⊓ stateSector G (Fock.numberSector (Mode (Fin 3) S) n) = ⊥ by
    rw [hbot, finrank_bot]
  rw [Submodule.eq_bot_iff]
  intro ψ hψ
  obtain ⟨hc, hs⟩ := Submodule.mem_inf.mp hψ
  rw [mem_colourless_iff] at hc
  have h1 : ψ 1 ∈ Fock.numberSector (Mode (Fin 3) S) n :=
    (Submodule.mem_pi.mp hs) 1 (Set.mem_univ _)
  have hfix := hc.2 h₀
  have hscale : diagHom ρ ord h₀ *ᵥ ψ 1 = Exact.omega ^ n • ψ 1 := by
    change Fock.secondQuant ord (diag (ρ h₀) (ρ h₀)) *ᵥ ψ 1 = _
    rw [hh₀, diag_smul_one, eq_sum_ket (ψ 1), Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.mulVec_smul, secondQuant_smul_one_ket, smul_comm]
    by_cases ht : ψ 1 t = 0
    · simp [ht]
    · rw [h1 t ht]
  rw [hscale] at hfix
  have hz : ψ 1 = 0 := by
    have h2 : (Exact.omega ^ n - 1) • ψ 1 = 0 := by rw [sub_smul, hfix, one_smul, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (omega_pow_ne_one hn))
  funext U
  rw [hc.1 U, hz, Matrix.mulVec_zero]
  rfl

/-! ### The second return `P V² P` -/

/-- For a finite colour group with an irreducible triplet in `SU(3)`, real when `m = 1` and with
no invariant in `3 ⊗ 3` when `m = 0`, every orthogonal projector onto the zero-flux sector gives
`P V² P = Ω` on the sector: the argument of Theorem 11.20. -/
theorem pvvp_eq_tally {G : Type} [Group G] [Fintype G] {S : Type} [Fintype S] [DecidableEq S]
    (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (hρ : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (hirr : (tripletRep ρ).IsIrreducible) (ord : LinearOrder (Mode (Fin 3) S)) (m : ℕ)
    (hm : (m = 1 ∧ ∀ U i j, conj (ρ U i j) = ρ U i j) ∨
      (m = 0 ∧ ∀ T : Matrix (Fin 3) (Fin 3) ℂ, (∀ U, ρ U * T * (ρ U)ᵀ = T) → T = 0))
    (P : (G → Finset (Mode (Fin 3) S) → ℂ) →ₗ[ℂ] (G → Finset (Mode (Fin 3) S) → ℂ))
    (hP1 : ∀ ψ, P ψ ∈ zeroFlux ρ ord) (hP2 : ∀ ψ ∈ zeroFlux ρ ord, P ψ = ψ)
    (hP3 : ∀ ψ φ, statePairing (P ψ) φ = statePairing ψ (P φ)) :
    ∀ ψ ∈ zeroFlux ρ ord, P (hop ρ ord (hop ρ ord ψ)) = atEachLink (tally ord m) ψ := by
  classical
  have hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ := fun g =>
    (Matrix.mem_specialUnitaryGroup_iff.mp (hρ g)).1
  have hmom := mtMoments G ρ hρ hirr
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpair_eq : ∀ p q : Fin 3 × Fin 3,
      (if p.1 = q.1 ∧ p.2 = q.2 then (1 : ℂ) else 0) = if p = q then 1 else 0 := by
    intro p q
    simp [Prod.ext_iff]
  have hsum : ∀ x : ℂ, x = (Fintype.card G : ℂ) * ((Fintype.card G : ℂ)⁻¹ * x) := fun x => by
    rw [mul_inv_cancel_left₀ hcard]
  have hUUb : ∀ p q : Fin 3 × Fin 3, ∑ U, ρ U p.1 p.2 * conj (ρ U q.1 q.2) =
      (Fintype.card G : ℂ) * (1 / 3) * if p = q then 1 else 0 := by
    intro p q
    have h := hmom.2.1 p.1 p.2 q.1 q.2
    rw [hpair_eq] at h
    rw [hsum (∑ U, _), h]
    ring
  have hUU : ∀ p q : Fin 3 × Fin 3, ∑ U, ρ U p.1 p.2 * ρ U q.1 q.2 =
      (Fintype.card G : ℂ) * ((m : ℂ) / 3) * if p = q then 1 else 0 := by
    intro p q
    rcases hm with ⟨rfl, hreal⟩ | ⟨rfl, hnone⟩
    · have h := hmom.2.2.1 hreal p.1 p.2 q.1 q.2
      rw [hpair_eq] at h
      rw [hsum (∑ U, _), h]
      push_cast
      ring
    · have h := hmom.2.2.2.1 hnone p.1 p.2 q.1 q.2
      rw [hsum (∑ U, _), h]
      push_cast
      ring
  have hsq := sum_hopAt_sq ord m hUU hUUb
  have htally : ∀ h : G × G, pairHom ρ ord h * tally ord m = tally ord m * pairHom ρ ord h := by
    intro h
    have := pairHom_mul_sum_sq hunit ord h
    rw [hsq, Matrix.mul_smul, Matrix.smul_mul] at this
    exact smul_right_injective _ hcard this
  have hΩmem : ∀ ψ ∈ zeroFlux ρ ord, atEachLink (tally ord m) ψ ∈ zeroFlux ρ ord := by
    intro ψ hψ
    rw [mem_zeroFlux_iff] at hψ ⊢
    refine ⟨fun U => ?_, fun h => ?_⟩
    · simp only [atEachLink, hψ.1 U]
    · simp only [atEachLink]
      rw [Matrix.mulVec_mulVec, htally, ← Matrix.mulVec_mulVec, hψ.2 h]
  have hpairV2 : ∀ ξ ∈ zeroFlux ρ ord, ∀ ψ ∈ zeroFlux ρ ord,
      statePairing ξ (hop ρ ord (hop ρ ord ψ)) =
        statePairing ξ (atEachLink (tally ord m) ψ) := by
    intro ξ hξ ψ hψ
    rw [const_of_mem_zeroFlux hξ, const_of_mem_zeroFlux hψ]
    have e1 : hop ρ ord (hop ρ ord (fun _ => ψ 1)) =
        fun U => (hopAt ord (ρ U) * hopAt ord (ρ U)) *ᵥ ψ 1 := by
      funext U
      simp only [hop, Matrix.mulVec_mulVec]
    have e2 : atEachLink (tally ord m) (fun _ : G => ψ 1) = fun _ : G => tally ord m *ᵥ ψ 1 :=
      rfl
    rw [e1, e2, statePairing_const_atEach, statePairing_const_atEach, hsq, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  intro ψ hψ
  exact proj_eq_of_orth hP1 hP2 hP3 (hΩmem ψ hψ) fun ξ hξ => hpairV2 ξ hξ ψ hψ

end ModelsGroups

end Artform
