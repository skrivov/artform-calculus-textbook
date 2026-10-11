import ArtformTextbook.Ch11.Moments

/-!
# The there-and-back tally (Theorem 11.20)

* **Projector.** An orthogonal projector `P` onto the zero-flux sector sends a state to the
  zero-flux state `p` with `χ - p` orthogonal to the sector (`ThereAndBack.proj_eq_of_orth`).
  For zero-flux states `ξ` (constant, value `ξ₁`) and `ψ` (value `ψ₁`) the pairings are
  `⟨ξ, V ψ⟩ = ⟨ξ₁, (Σ_U V_U) ψ₁⟩` and `⟨ξ, V² ψ⟩ = ⟨ξ₁, (Σ_U V_U²) ψ₁⟩`.
* **Moments.** `V_U = Σ_p U_p A_p + Σ_p conj(U_p) A_p†` over the pairs `p = (c, c')`, so the
  first moment gives `Σ_U V_U = 0` and the second moments give `Σ_U V_U² = |G| Ω`
  (`ThereAndBack.sum_hopAt_sq`). The average of `V_U²` commutes with the gauge pairs, so `Ω`
  keeps the sector.
* **Blocks.** The table `U ↦ U_{cc'}` is in the block of the triplet and `U ↦ conj(U_{cc'})` in
  that of the conjugate triplet; the electric energy multiplies both blocks by `E₃`.
-/

namespace Artform

open scoped Matrix ComplexConjugate

namespace ThereAndBack

open Edge

variable {S : Type*} [Fintype S] [DecidableEq S] {G : Type*} [Fintype G]

/-! ### Pairings and the projector -/

theorem statePairing_conj {M : Type*} [Fintype M] (ψ φ : G → Finset M → ℂ) :
    conj (statePairing ψ φ) = statePairing φ ψ := by
  simp only [statePairing, coeffPairing, map_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun n _ => ?_
  ring

theorem statePairing_sub_right {M : Type*} [Fintype M] (ψ φ φ' : G → Finset M → ℂ) :
    statePairing ψ (φ - φ') = statePairing ψ φ - statePairing ψ φ' := by
  simp only [statePairing, coeffPairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- A self-adjoint linear map that fixes a subspace and has its values there kills the vectors
orthogonal to it. -/
theorem proj_eq_zero_of_orth {M : Type*} [Fintype M]
    {Z : Submodule ℂ (G → Finset M → ℂ)} {P : (G → Finset M → ℂ) →ₗ[ℂ] (G → Finset M → ℂ)}
    (hP1 : ∀ ψ, P ψ ∈ Z) (hP2 : ∀ ψ ∈ Z, P ψ = ψ)
    (hP3 : ∀ ψ φ, statePairing (P ψ) φ = statePairing ψ (P φ)) {χ : G → Finset M → ℂ}
    (hχ : ∀ ξ ∈ Z, statePairing ξ χ = 0) : P χ = 0 := by
  apply statePairing_self_eq_zero
  rw [hP3, hP2 _ (hP1 χ), ← statePairing_conj, hχ _ (hP1 χ), map_zero]

/-- An orthogonal projector onto `Z` sends `χ` to the vector `p` of `Z` with `χ - p` orthogonal
to `Z`. -/
theorem proj_eq_of_orth {M : Type*} [Fintype M]
    {Z : Submodule ℂ (G → Finset M → ℂ)} {P : (G → Finset M → ℂ) →ₗ[ℂ] (G → Finset M → ℂ)}
    (hP1 : ∀ ψ, P ψ ∈ Z) (hP2 : ∀ ψ ∈ Z, P ψ = ψ)
    (hP3 : ∀ ψ φ, statePairing (P ψ) φ = statePairing ψ (P φ)) {χ p : G → Finset M → ℂ}
    (hp : p ∈ Z) (hχ : ∀ ξ ∈ Z, statePairing ξ χ = statePairing ξ p) : P χ = p := by
  have h := proj_eq_zero_of_orth hP1 hP2 hP3 (χ := χ - p) fun ξ hξ => by
    rw [statePairing_sub_right, hχ ξ hξ, sub_self]
  rw [map_sub, hP2 p hp, sub_eq_zero] at h
  exact h

/-- The pairing of a constant state with a state acted on link by link. -/
theorem statePairing_const_atEach {M : Type*} [Fintype M] (ξ₁ ψ₁ : Finset M → ℂ)
    (X : G → Matrix (Finset M) (Finset M) ℂ) :
    statePairing (fun _ : G => ξ₁) (fun U => X U *ᵥ ψ₁) = coeffPairing ξ₁ ((∑ U, X U) *ᵥ ψ₁) := by
  simp only [statePairing, Matrix.sum_mulVec, Fock.coeffPairing_sum_right]

/-! ### The hop over pairs of colours -/

section Hop

variable {N : Type*} [Fintype N]

/-- Expanding a sum of products over pairs with a moment `Σ_U f_U(p) g_U(q) = k δ_{pq}`. -/
theorem sum_mul_sums {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : G → ι → ℂ)
    (X Y : ι → Matrix N N ℂ) (k : ℂ) (h : ∀ p q, ∑ U, f U p * g U q = k * if p = q then 1 else 0) :
    ∑ U, (∑ p, f U p • X p) * (∑ q, g U q • Y q) = k • ∑ p, X p * Y p := by
  simp only [Finset.sum_mul_sum, smul_mul_smul_comm]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, h, mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem annihilation_conjTranspose {M : Type*} [DecidableEq M] (ord : LinearOrder M)
    (m : M) : (Fock.annihilation ord m)ᴴ = Fock.creation ord m := by
  rw [← Fock.conjTranspose_creation, Matrix.conjTranspose_conjTranspose]

/-- `A_{cc'}† = Σ_s a†_{xc's} a_{ycs}`. -/
theorem hopA_conjTranspose (ord : LinearOrder (Mode (Fin 3) S)) (c c' : Fin 3) :
    (hopA ord c c')ᴴ =
      ∑ s, Fock.creation ord (Sum.inl (c', s)) * Fock.annihilation ord (Sum.inr (c, s)) := by
  rw [hopA, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.conjTranspose_mul, Fock.conjTranspose_creation, annihilation_conjTranspose]

/-- `V_U = Σ_p U_p A_p + Σ_p conj(U_p) A_p†` over the pairs `p = (c, c')`. -/
theorem hopAt_eq_pairs (ord : LinearOrder (Mode (Fin 3) S)) (U : Matrix (Fin 3) (Fin 3) ℂ) :
    hopAt ord U = (∑ p : Fin 3 × Fin 3, U p.1 p.2 • hopA ord p.1 p.2) +
      ∑ p : Fin 3 × Fin 3, conj (U p.1 p.2) • (hopA ord p.1 p.2)ᴴ := by
  rw [hopAt, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [hopA_conjTranspose]
  simp only [hopA, Finset.smul_sum]

/-- The tally over pairs. -/
theorem tally_eq_pairs (ord : LinearOrder (Mode (Fin 3) S)) (m : ℕ) :
    tally ord m = (1 / 3 : ℂ) • (∑ p : Fin 3 × Fin 3,
        ((hopA ord p.1 p.2)ᴴ * hopA ord p.1 p.2 + hopA ord p.1 p.2 * (hopA ord p.1 p.2)ᴴ)) +
      ((m : ℂ) / 3) • (∑ p : Fin 3 × Fin 3,
        (hopA ord p.1 p.2 * hopA ord p.1 p.2 + (hopA ord p.1 p.2)ᴴ * (hopA ord p.1 p.2)ᴴ)) := by
  rw [tally, Fintype.sum_prod_type, Fintype.sum_prod_type]

variable [Group G]

/-- The first moment: `Σ_U V_U = 0` when `Σ_U U = 0`. -/
theorem sum_hopAt_eq_zero (ord : LinearOrder (Mode (Fin 3) S)) {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (h1 : ∑ U, ρ U = 0) : ∑ U, hopAt ord (ρ U) = 0 := by
  simp only [hopAt_eq_pairs, Finset.sum_add_distrib]
  have h1' : ∀ p : Fin 3 × Fin 3, ∑ U, ρ U p.1 p.2 = 0 := fun p => by
    rw [← Matrix.sum_apply, h1, Matrix.zero_apply]
  have hA : ∑ U, ∑ p : Fin 3 × Fin 3, ρ U p.1 p.2 • hopA ord p.1 p.2 = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, h1', zero_smul, Finset.sum_const_zero]
  have hB : ∑ U, ∑ p : Fin 3 × Fin 3, conj (ρ U p.1 p.2) • (hopA ord p.1 p.2)ᴴ = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← map_sum, h1', map_zero, zero_smul, Finset.sum_const_zero]
  rw [hA, hB, add_zero]

/-- The second moments: `Σ_U V_U² = |G| Ω`. -/
theorem sum_hopAt_sq (ord : LinearOrder (Mode (Fin 3) S)) {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (m : ℕ)
    (hUU : ∀ p q : Fin 3 × Fin 3, ∑ U, ρ U p.1 p.2 * ρ U q.1 q.2 =
      (Fintype.card G : ℂ) * ((m : ℂ) / 3) * if p = q then 1 else 0)
    (hUUb : ∀ p q : Fin 3 × Fin 3, ∑ U, ρ U p.1 p.2 * conj (ρ U q.1 q.2) =
      (Fintype.card G : ℂ) * (1 / 3) * if p = q then 1 else 0) :
    ∑ U, hopAt ord (ρ U) * hopAt ord (ρ U) = (Fintype.card G : ℂ) • tally ord m := by
  have hUbU : ∀ p q : Fin 3 × Fin 3, ∑ U, conj (ρ U p.1 p.2) * ρ U q.1 q.2 =
      (Fintype.card G : ℂ) * (1 / 3) * if p = q then 1 else 0 := by
    intro p q
    rw [Finset.sum_congr rfl fun U _ => mul_comm _ _, hUUb q p]
    by_cases hpq : p = q
    · simp [hpq]
    · simp [hpq, Ne.symm hpq]
  have hUbUb : ∀ p q : Fin 3 × Fin 3, ∑ U, conj (ρ U p.1 p.2) * conj (ρ U q.1 q.2) =
      (Fintype.card G : ℂ) * ((m : ℂ) / 3) * if p = q then 1 else 0 := by
    intro p q
    have := congrArg conj (hUU p q)
    simp only [map_sum, map_mul, map_natCast, map_div₀, map_ofNat] at this
    rw [this]
    split_ifs <;> simp
  simp only [hopAt_eq_pairs, add_mul, mul_add, Finset.sum_add_distrib]
  rw [sum_mul_sums _ _ _ _ _ hUU, sum_mul_sums _ _ _ _ _ hUUb, sum_mul_sums _ _ _ _ _ hUbU,
    sum_mul_sums _ _ _ _ _ hUbUb, tally_eq_pairs]
  simp only [smul_add, Finset.sum_add_distrib, smul_smul]
  module

end Hop

/-! ### The hop on the zero-flux sector -/

section Sector

variable {S : Type*} [Fintype S] [DecidableEq S] [Group G]

omit [Fintype G] in
theorem const_of_mem_zeroFlux {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    {ord : LinearOrder (Mode (Fin 3) S)} {ψ : G → Finset (Mode (Fin 3) S) → ℂ}
    (hψ : ψ ∈ zeroFlux ρ ord) : ψ = fun _ => ψ 1 :=
  funext fun U => ((mem_zeroFlux_iff ρ ord ψ).mp hψ).1 U

/-- `⟨ξ, V ψ⟩ = 0` for zero-flux states, when the first moment vanishes. -/
theorem statePairing_hop_eq_zero (ord : LinearOrder (Mode (Fin 3) S))
    {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ} (h1 : ∑ U, ρ U = 0) {ξ ψ : G → Finset (Mode (Fin 3) S) → ℂ}
    (hξ : ξ ∈ zeroFlux ρ ord) (hψ : ψ ∈ zeroFlux ρ ord) :
    statePairing ξ (hop ρ ord ψ) = 0 := by
  rw [const_of_mem_zeroFlux hξ, const_of_mem_zeroFlux hψ]
  change statePairing (fun _ : G => ξ 1) (fun U => hopAt ord (ρ U) *ᵥ ψ 1) = 0
  rw [statePairing_const_atEach, sum_hopAt_eq_zero ord h1, Matrix.zero_mulVec,
    Blocks.coeffPairing_zero_right]

omit [Fintype G] in
/-- The gauge pairs move the hop: `Γ(D) V_U = V_{h_y U h_x⁻¹} Γ(D)`. -/
theorem pairHom_mul_hopAt {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ) (ord : LinearOrder (Mode (Fin 3) S))
    (hx hy U : G) :
    pairHom ρ ord (hx, hy) * hopAt ord (ρ U) =
      hopAt ord (ρ (hy * U * hx⁻¹)) * pairHom ρ ord (hx, hy) := by
  rw [← hopAt_covariant hρ ord hx hy U, pairHom_apply, mul_assoc _ (gammaY ord (ρ hy))⁻¹,
    ← Matrix.mul_inv_rev, mul_assoc _ (gammaX ord (ρ hx) * gammaY ord (ρ hy))⁻¹,
    gammaXY_mul_inv hρ, mul_one]

/-- The average of `V_U²` commutes with the gauge pairs. -/
theorem pairHom_mul_sum_sq {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ) (ord : LinearOrder (Mode (Fin 3) S))
    (h : G × G) :
    pairHom ρ ord h * ∑ U, hopAt ord (ρ U) * hopAt ord (ρ U) =
      (∑ U, hopAt ord (ρ U) * hopAt ord (ρ U)) * pairHom ρ ord h := by
  obtain ⟨hx, hy⟩ := h
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv ((Equiv.mulLeft hy).trans (Equiv.mulRight hx⁻¹)) _ _ fun U => ?_
  simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight]
  calc pairHom ρ ord (hx, hy) * (hopAt ord (ρ U) * hopAt ord (ρ U))
      = (pairHom ρ ord (hx, hy) * hopAt ord (ρ U)) * hopAt ord (ρ U) :=
        (Matrix.mul_assoc _ _ _).symm
    _ = (hopAt ord (ρ (hy * U * hx⁻¹)) * pairHom ρ ord (hx, hy)) * hopAt ord (ρ U) := by
        rw [pairHom_mul_hopAt hρ]
    _ = hopAt ord (ρ (hy * U * hx⁻¹)) * (pairHom ρ ord (hx, hy) * hopAt ord (ρ U)) :=
        Matrix.mul_assoc _ _ _
    _ = hopAt ord (ρ (hy * U * hx⁻¹)) *
          (hopAt ord (ρ (hy * U * hx⁻¹)) * pairHom ρ ord (hx, hy)) := by
        rw [pairHom_mul_hopAt hρ]
    _ = _ := (Matrix.mul_assoc _ _ _).symm

omit [Fintype G] in
theorem entry_mem_block (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (c c' : Fin 3) :
    (fun U => ρ U c c') ∈ block (tripletRep ρ) := by
  refine mem_block.mpr ⟨Matrix.toLin' (Matrix.single c' c 1), ?_⟩
  funext U
  rw [blockTable, show tripletRep ρ U = Matrix.toLin' (ρ U) from rfl, Module.End.mul_eq_comp,
    ← Matrix.toLin'_mul, Matrix.trace_toLin'_eq, Matrix.trace_single_mul, one_smul]

omit [Fintype G] in
theorem conj_entry_mem_block (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (c c' : Fin 3) :
    (fun U => conj (ρ U c c')) ∈ block (conjTripletRep ρ) := by
  refine mem_block.mpr ⟨Matrix.toLin' (Matrix.single c' c 1), ?_⟩
  funext U
  rw [blockTable, show conjTripletRep ρ U = Matrix.toLin' ((ρ U).map (starRingEnd ℂ)) from rfl,
    Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.trace_toLin'_eq, Matrix.trace_single_mul,
    one_smul, Matrix.map_apply]

omit [Fintype G] in
/-- The hop moves the link's table of a zero-flux state into the triplet block or its
conjugate. -/
theorem hop_mem_blocks (ord : LinearOrder (Mode (Fin 3) S)) (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    {ψ : G → Finset (Mode (Fin 3) S) → ℂ} (hψ : ψ ∈ zeroFlux ρ ord) (n : Finset (Mode (Fin 3) S)) :
    (fun U => hop ρ ord ψ U n) ∈ block (tripletRep ρ) ⊔ block (conjTripletRep ρ) := by
  have h : (fun U => hop ρ ord ψ U n) =
      (∑ p : Fin 3 × Fin 3, (hopA ord p.1 p.2 *ᵥ ψ 1) n • fun U => ρ U p.1 p.2) +
        ∑ p : Fin 3 × Fin 3, ((hopA ord p.1 p.2)ᴴ *ᵥ ψ 1) n • fun U => conj (ρ U p.1 p.2) := by
    funext U
    rw [const_of_mem_zeroFlux hψ]
    simp only [hop, hopAt_eq_pairs, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
      Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    congr 1 <;> refine Finset.sum_congr rfl fun p _ => ?_ <;> ring
  rw [h]
  exact Submodule.add_mem_sup
    (Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (entry_mem_block ρ p.1 p.2))
    (Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (conj_entry_mem_block ρ p.1 p.2))

end Sector

end ThereAndBack

/-! ### Diagonal one-quark operators -/

namespace Fock

variable {M : Type*} [Fintype M] [DecidableEq M]

theorem trProd_diagonal (ord : LinearOrder M) (e : M → ℂ) (L : List M) :
    trProd ord (Matrix.diagonal e) L = (L.map e).prod • crProd ord L := by
  induction L with
  | nil => simp [trProd, crProd]
  | cons a L ih =>
    rw [trProd, List.map_cons, List.prod_cons, ← trProd, ih, transformedCreation]
    simp only [Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    rw [smul_mul_smul_comm, crProd, crProd, List.map_cons, List.prod_cons, List.map_cons,
      List.prod_cons]

omit [Fintype M] [DecidableEq M] in
theorem prod_sort_map (ord : LinearOrder M) (n : Finset M) (f : M → ℂ) :
    (((letI := ord; n.sort).map f).prod) = ∏ m ∈ n, f m := by
  let := ord
  rw [Finset.prod_eq_multiset_prod, ← Finset.sort_eq n (· ≤ ·), Multiset.map_coe,
    Multiset.prod_coe]

/-- The second quantization of a diagonal matrix multiplies each table by the product of the
diagonal entries of its occupied modes. -/
theorem secondQuant_diagonal (ord : LinearOrder M) (e : M → ℂ) :
    secondQuant ord (Matrix.diagonal e) = Matrix.diagonal fun n => ∏ m ∈ n, e m := by
  apply ext_ket
  intro n
  rw [secondQuant_mulVec_ket, trProd_diagonal, Matrix.smul_mulVec, crProd_sort_mulVec_vacuum,
    prod_sort_map, ket, Matrix.diagonal_mulVec_single, mul_one]
  funext n'
  simp [Pi.single_apply]

/-- The second quantization of a diagonal one-quark operator adds the diagonal entries of the
occupied modes. -/
theorem dGamma_diagonal (ord : LinearOrder M) (s : M → ℂ) :
    dGamma ord (Matrix.diagonal s) = Matrix.diagonal fun n => ∑ m ∈ n, s m := by
  rw [dGamma]
  simp only [Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, creation_mul_annihilation]
  ext n' n
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_mem]
  · simp

end Fock

/-! ### The coin as a diagonalized operator -/

namespace ThereAndBack

open Edge Polynomial

section Diag

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

/-- The signs `+1` on the modes at `x` and `-1` on those at `y`. -/
def sgn (m : Mode C S) : ℂ := if m.isLeft then 1 else -1

/-- The eigenvectors of the one-quark hop: `Q_U = (1/√2) [[1, 1], [U ⊗ 1, -(U ⊗ 1)]]`. -/
noncomputable def Qm (U : Matrix C C ℂ) : Matrix (Mode C S) (Mode C S) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • Matrix.fromBlocks 1 1 (Matrix.kroneckerMap (· * ·) U 1)
    (-(Matrix.kroneckerMap (· * ·) U 1))

omit [Fintype C] [Fintype S] in
theorem diagonal_sgn : (Matrix.diagonal sgn : Matrix (Mode C S) (Mode C S) ℂ) =
    Matrix.fromBlocks 1 0 0 (-1) := by
  ext (a | b) (a' | b') <;> simp [sgn, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem star_inv_sqrt_two : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

theorem inv_sqrt_two_mul_self :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, Exact.sqrt_two_mul_self]
  norm_num

omit [Fintype C] [Fintype S] in
theorem star_Qm (U : Matrix C C ℂ) :
    star (Qm U : Matrix (Mode C S) (Mode C S) ℂ) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
      Matrix.fromBlocks 1 (Matrix.kroneckerMap (· * ·) (star U) 1) 1
        (-(Matrix.kroneckerMap (· * ·) (star U) 1)) := by
  rw [Qm, star_smul, star_inv_sqrt_two, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_neg, Matrix.conjTranspose_kronecker,
    Matrix.star_eq_conjTranspose]

theorem Qm_mem_unitaryGroup {U : Matrix C C ℂ} (hU : U ∈ Matrix.unitaryGroup C ℂ) :
    (Qm U : Matrix (Mode C S) (Mode C S) ℂ) ∈ Matrix.unitaryGroup (Mode C S) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_Qm, Qm, smul_mul_smul_comm, inv_sqrt_two_mul_self,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    Fock.kron_one_mul, Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.one_kronecker_one,
    add_neg_cancel]
  ext (a | b) (a' | b') <;> simp [Matrix.one_apply] <;> split_ifs <;> norm_num

/-- `K_U = Q_U diag(1, -1) Q_U†`. -/
theorem coinK_eq_conj (U : Matrix C C ℂ) :
    (coinK U : Matrix (Mode C S) (Mode C S) ℂ) =
      Qm U * Matrix.diagonal sgn * star (Qm U) := by
  rw [diagonal_sgn, star_Qm, Qm, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_sqrt_two_mul_self, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, neg_neg, add_neg_cancel]
  ext (a | b) (a' | b') <;> simp [coinK, Matrix.smul_apply] <;> ring

end Diag

section Exp

open NormedSpace

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

/-- The occupation sums `t(n) = Σ_{m ∈ n} s(m)`: the quarks at `x` minus those at `y`, in the
eigenbasis of the hop. -/
def occSum (n : Finset (Mode C S)) : ℂ := ∑ m ∈ n, sgn m

theorem exp_smul_conj {N : Type*} [Fintype N] [DecidableEq N] (Q X : Matrix N N ℂ) (hQ : IsUnit Q)
    (c : ℂ) : exp (c • (Q * X * Q⁻¹)) = Q * exp (c • X) * Q⁻¹ := by
  rw [show c • (Q * X * Q⁻¹) = Q * (c • X) * Q⁻¹ by rw [Matrix.mul_smul, Matrix.smul_mul],
    Matrix.exp_conj _ _ hQ]

theorem exp_smul_diagonal {N : Type*} [Fintype N] [DecidableEq N] (c : ℂ) (v : N → ℂ) :
    exp (c • Matrix.diagonal v) = Matrix.diagonal fun i => Complex.exp (c * v i) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]

theorem star_Qm_eq_inv {U : Matrix C C ℂ} (hU : U ∈ Matrix.unitaryGroup C ℂ) :
    star (Qm U : Matrix (Mode C S) (Mode C S) ℂ) = (Qm U)⁻¹ := by
  rw [Fock.inv_eq_conjTranspose_of_mem (Qm_mem_unitaryGroup hU), Matrix.star_eq_conjTranspose]

/-- `V_U = Γ(Q_U) diag(t) Γ(Q_U)⁻¹`. -/
theorem hopAt_eq_conj (ord : LinearOrder (Mode C S)) {U : Matrix C C ℂ}
    (hU : U ∈ Matrix.unitaryGroup C ℂ) :
    hopAt ord U = Fock.secondQuant ord (Qm U) * Matrix.diagonal occSum *
      (Fock.secondQuant ord (Qm U))⁻¹ := by
  rw [hopAt_eq_dGamma, coinK_eq_conj, ← Fock.secondQuant_conj_dGamma ord (Qm_mem_unitaryGroup hU),
    Fock.dGamma_diagonal]
  rfl

/-- `e^{iθ K_U} = Q_U diag(e^{iθ s}) Q_U⁻¹`. -/
theorem exp_coinK {U : Matrix C C ℂ} (hU : U ∈ Matrix.unitaryGroup C ℂ) (c : ℂ) :
    exp (c • (coinK U : Matrix (Mode C S) (Mode C S) ℂ)) =
      Qm U * Matrix.diagonal (fun m => Complex.exp (c * sgn m)) * (Qm U)⁻¹ := by
  rw [coinK_eq_conj, star_Qm_eq_inv hU, exp_smul_conj _ _
    (Fock.isUnit_of_mem_unitaryGroup (Qm_mem_unitaryGroup hU)), exp_smul_diagonal]

/-- `Γ(e^{c K_U}) = e^{c V_U}`. -/
theorem secondQuant_exp_coinK (ord : LinearOrder (Mode C S)) {U : Matrix C C ℂ}
    (hU : U ∈ Matrix.unitaryGroup C ℂ) (c : ℂ) :
    Fock.secondQuant ord (exp (c • coinK U)) = exp (c • hopAt ord U) := by
  have hQ := Fock.isUnit_of_mem_unitaryGroup (Qm_mem_unitaryGroup (S := S) hU)
  have hΓ := Fock.isUnit_of_mem_unitaryGroup
    (Fock.secondQuant_mem_unitaryGroup ord (Qm_mem_unitaryGroup (S := S) hU))
  rw [hopAt_eq_conj ord hU, exp_smul_conj _ _ hΓ, exp_smul_diagonal, exp_coinK hU,
    ← Fock.secondQuant_mul, ← Fock.secondQuant_mul, Fock.secondQuant_diagonal,
    Fock.secondQuant_inv ord hQ]
  congr 3
  funext n
  rw [occSum, Finset.mul_sum, Complex.exp_sum]

/-- `e^{iθ K_U} = cos θ + i sin θ K_U`. -/
theorem exp_coinK_eq {U : Matrix C C ℂ} (hU : U ∈ Matrix.unitaryGroup C ℂ) (θ : ℝ) :
    exp (((θ : ℂ) * Complex.I) • (coinK U : Matrix (Mode C S) (Mode C S) ℂ)) =
      (Real.cos θ : ℂ) • 1 + ((Real.sin θ : ℂ) * Complex.I) • coinK U := by
  have hQ := Fock.isUnit_of_mem_unitaryGroup (Qm_mem_unitaryGroup (S := S) hU)
  have hdiag : Matrix.diagonal (fun m : Mode C S => Complex.exp ((θ : ℂ) * Complex.I * sgn m)) =
      (Real.cos θ : ℂ) • 1 + ((Real.sin θ : ℂ) * Complex.I) • Matrix.diagonal sgn := by
    ext m m'
    by_cases h : m = m'
    · subst h
      simp only [sgn, Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one]
      split_ifs
      · rw [mul_one, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin, mul_one]
      · rw [mul_neg_one, ← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
          Complex.ofReal_cos, Complex.ofReal_sin]
        ring
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  rw [exp_coinK hU, hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hQ),
    Matrix.mul_smul, Matrix.smul_mul, ← star_Qm_eq_inv hU, ← coinK_eq_conj]

/-- The native coin is the member `θ = π/4` of the family: `e^{iπ/4 K_U} = W_U`. -/
theorem exp_pi_div_four_coinK {U : Matrix C C ℂ} (hU : U ∈ Matrix.unitaryGroup C ℂ) :
    exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • (coinK U : Matrix (Mode C S) (Mode C S) ℂ)) =
      coinW U := by
  rw [exp_coinK_eq hU, Real.cos_pi_div_four, Real.sin_pi_div_four, coinW, smul_add, smul_smul]
  have h : ((Real.sqrt 2 / 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [Exact.inv_sqrt_two_eq]
    push_cast
    ring
  rw [h, mul_comm]

end Exp

section Bound

open NormedSpace

/-- `|e^{ix} - 1 - ix + x²/2| ≤ 4|x|³` for real `x`. -/
theorem norm_exp_I_sub_le (x : ℝ) :
    ‖Complex.exp (x * Complex.I) - 1 - x * Complex.I + (x : ℂ) ^ 2 / 2‖ ≤ 4 * |x| ^ 3 := by
  rcases le_or_gt |x| 1 with hx | hx
  · have hz : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hx
    have h := Complex.exp_bound hz (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
        1 + x * Complex.I - (x : ℂ) ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial, mul_pow, Complex.I_sq]
      ring
    rw [hsum] at h
    have heq : Complex.exp (x * Complex.I) - 1 - x * Complex.I + (x : ℂ) ^ 2 / 2 =
        Complex.exp (x * Complex.I) - (1 + x * Complex.I - (x : ℂ) ^ 2 / 2) := by ring
    rw [heq]
    refine h.trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h3 : 0 ≤ |x| ^ 3 := by positivity
    norm_num
    nlinarith
  · have h1 : 1 ≤ |x| := hx.le
    calc ‖Complex.exp (x * Complex.I) - 1 - x * Complex.I + (x : ℂ) ^ 2 / 2‖
        ≤ ‖Complex.exp (x * Complex.I)‖ + ‖(1 : ℂ)‖ + ‖(x : ℂ) * Complex.I‖ +
            ‖(x : ℂ) ^ 2 / 2‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ = 1 + 1 + |x| + |x| ^ 2 / 2 := by
          rw [Complex.norm_exp_ofReal_mul_I, norm_one, norm_mul, Complex.norm_I, mul_one,
            norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
      _ ≤ 4 * |x| ^ 3 := by
          have h2 : |x| ≤ |x| ^ 2 := by nlinarith
          have h3 : |x| ^ 2 ≤ |x| ^ 3 := by nlinarith
          nlinarith

/-- A matrix with entries of size at most `c` multiplies the norm by at most `|N| c`. -/
theorem norm_mulVec_le {N : Type*} [Fintype N] (X : Matrix N N ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hX : ∀ i j, ‖X i j‖ ≤ c) (v : N → ℂ) :
    ‖X *ᵥ v‖ ≤ (Fintype.card N * c) * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  calc ‖(X *ᵥ v) i‖ = ‖∑ j, X i j * v j‖ := rfl
    _ ≤ ∑ j, ‖X i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : N, c * ‖v‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hX i j) (norm_le_pi_norm v j) (norm_nonneg _) hc
    _ = (Fintype.card N * c) * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

omit [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] in
/-- The occupation sums are real. -/
theorem occSum_eq (n : Finset (Mode C S)) :
    occSum n = ((∑ m ∈ n, if m.isLeft then (1 : ℝ) else -1 : ℝ) : ℂ) := by
  rw [occSum]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [sgn]
  split_ifs <;> simp

/-- The second-order remainder of `e^{iθ V_U}`, in the eigenbasis of the hop. -/
theorem exp_hopAt_remainder (ord : LinearOrder (Mode C S)) {U : Matrix C C ℂ}
    (hU : U ∈ Matrix.unitaryGroup C ℂ) (θ : ℝ) :
    exp (((θ : ℂ) * Complex.I) • hopAt ord U) - 1 - ((θ : ℂ) * Complex.I) • hopAt ord U -
        (((θ : ℂ) * Complex.I) ^ 2 / 2) • (hopAt ord U * hopAt ord U) =
      Fock.secondQuant ord (Qm U) * Matrix.diagonal (fun n =>
        Complex.exp ((θ : ℂ) * Complex.I * occSum n) - 1 - (θ : ℂ) * Complex.I * occSum n -
          ((θ : ℂ) * Complex.I) ^ 2 / 2 * (occSum n * occSum n)) *
        (Fock.secondQuant ord (Qm U))⁻¹ := by
  have hΓ := Fock.isUnit_of_mem_unitaryGroup
    (Fock.secondQuant_mem_unitaryGroup ord (Qm_mem_unitaryGroup (S := S) hU))
  have hV := hopAt_eq_conj ord hU
  set Γ := Fock.secondQuant ord (Qm U : Matrix (Mode C S) (Mode C S) ℂ)
  have hinv : Γ⁻¹ * Γ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hΓ)
  have hinv' : Γ * Γ⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hΓ)
  have hE : exp (((θ : ℂ) * Complex.I) • hopAt ord U) =
      Γ * Matrix.diagonal (fun n => Complex.exp ((θ : ℂ) * Complex.I * occSum n)) * Γ⁻¹ := by
    rw [hV, exp_smul_conj _ _ hΓ, exp_smul_diagonal]
  have hVV : hopAt ord U * hopAt ord U =
      Γ * Matrix.diagonal (fun n => occSum n * occSum n) * Γ⁻¹ := by
    rw [hV, show Γ * Matrix.diagonal occSum * Γ⁻¹ * (Γ * Matrix.diagonal occSum * Γ⁻¹) =
        Γ * Matrix.diagonal occSum * (Γ⁻¹ * Γ) * Matrix.diagonal occSum * Γ⁻¹ by
      simp only [Matrix.mul_assoc], hinv, Matrix.mul_one, Matrix.mul_assoc Γ,
      Matrix.diagonal_mul_diagonal, Matrix.mul_assoc]
  have hdiag : Matrix.diagonal (fun n : Finset (Mode C S) =>
        Complex.exp ((θ : ℂ) * Complex.I * occSum n) - 1 - (θ : ℂ) * Complex.I * occSum n -
          ((θ : ℂ) * Complex.I) ^ 2 / 2 * (occSum n * occSum n)) =
      Matrix.diagonal (fun n : Finset (Mode C S) =>
          Complex.exp ((θ : ℂ) * Complex.I * occSum n)) - 1 -
        ((θ : ℂ) * Complex.I) • Matrix.diagonal occSum -
        (((θ : ℂ) * Complex.I) ^ 2 / 2) • Matrix.diagonal (fun n => occSum n * occSum n) := by
    ext n n'
    by_cases h : n = n'
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  rw [hE, hVV, hV, hdiag]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hinv']

end Bound

section Bound2

open NormedSpace

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

/-- The remainder of `e^{iθ V_U}` is of order `θ³`, entry by entry. -/
theorem norm_remainder_apply_le (ord : LinearOrder (Mode C S)) {U : Matrix C C ℂ}
    (hU : U ∈ Matrix.unitaryGroup C ℂ) (θ : ℝ) (i j : Finset (Mode C S)) :
    ‖(exp (((θ : ℂ) * Complex.I) • hopAt ord U) - 1 - ((θ : ℂ) * Complex.I) • hopAt ord U -
        (((θ : ℂ) * Complex.I) ^ 2 / 2) • (hopAt ord U * hopAt ord U) :
          Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ) i j‖ ≤
      (∑ i, ∑ j, ∑ k, ‖Fock.secondQuant ord (Qm U) i k‖ *
        ‖(Fock.secondQuant ord (Qm U))⁻¹ k j‖ * (4 * ‖occSum k‖ ^ 3)) * |θ| ^ 3 := by
  rw [exp_hopAt_remainder ord hU, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  set Γ := Fock.secondQuant ord (Qm U : Matrix (Mode C S) (Mode C S) ℂ)
  have hf : ∀ k : Finset (Mode C S), ‖Complex.exp ((θ : ℂ) * Complex.I * occSum k) - 1 -
      (θ : ℂ) * Complex.I * occSum k - ((θ : ℂ) * Complex.I) ^ 2 / 2 * (occSum k * occSum k)‖ ≤
        4 * ‖occSum k‖ ^ 3 * |θ| ^ 3 := by
    intro k
    set t : ℝ := ∑ m ∈ k, if m.isLeft then (1 : ℝ) else -1
    have ht : occSum k = (t : ℂ) := occSum_eq k
    have := norm_exp_I_sub_le (θ * t)
    rw [ht]
    have heq : Complex.exp ((θ : ℂ) * Complex.I * t) - 1 - (θ : ℂ) * Complex.I * t -
        ((θ : ℂ) * Complex.I) ^ 2 / 2 * ((t : ℂ) * t) =
        Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) - 1 - ((θ * t : ℝ) : ℂ) * Complex.I +
          ((θ * t : ℝ) : ℂ) ^ 2 / 2 := by
      push_cast
      rw [show (θ : ℂ) * Complex.I * t = θ * t * Complex.I by ring, mul_pow, Complex.I_sq]
      ring
    rw [heq]
    refine this.trans (le_of_eq ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    ring
  calc ‖∑ k, Γ i k * (Complex.exp ((θ : ℂ) * Complex.I * occSum k) - 1 -
        (θ : ℂ) * Complex.I * occSum k - ((θ : ℂ) * Complex.I) ^ 2 / 2 * (occSum k * occSum k)) *
          Γ⁻¹ k j‖
      ≤ ∑ k, ‖Γ i k‖ * ‖Γ⁻¹ k j‖ * (4 * ‖occSum k‖ ^ 3) * |θ| ^ 3 := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul, norm_mul]
        calc ‖Γ i k‖ * ‖Complex.exp ((θ : ℂ) * Complex.I * occSum k) - 1 -
              (θ : ℂ) * Complex.I * occSum k -
                ((θ : ℂ) * Complex.I) ^ 2 / 2 * (occSum k * occSum k)‖ * ‖Γ⁻¹ k j‖
            ≤ ‖Γ i k‖ * (4 * ‖occSum k‖ ^ 3 * |θ| ^ 3) * ‖Γ⁻¹ k j‖ := by
              gcongr
              exact hf k
          _ = ‖Γ i k‖ * ‖Γ⁻¹ k j‖ * (4 * ‖occSum k‖ ^ 3) * |θ| ^ 3 := by ring
    _ = (∑ k, ‖Γ i k‖ * ‖Γ⁻¹ k j‖ * (4 * ‖occSum k‖ ^ 3)) * |θ| ^ 3 := by
        rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ∑ k, ‖Γ i k‖ * ‖Γ⁻¹ k j‖ * (4 * ‖occSum k‖ ^ 3)) * |θ| ^ 3 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine (Finset.single_le_sum (f := fun j => ∑ k, ‖Γ i k‖ * ‖Γ⁻¹ k j‖ *
          (4 * ‖occSum k‖ ^ 3)) (fun j _ => by positivity) (Finset.mem_univ j)).trans ?_
        exact Finset.single_le_sum (f := fun i => ∑ j, ∑ k, ‖Γ i k‖ * ‖Γ⁻¹ k j‖ *
          (4 * ‖occSum k‖ ^ 3)) (fun i _ => by positivity) (Finset.mem_univ i)

end Bound2

section Energy

variable {G : Type*} [Fintype G] {S : Type*} [Fintype S] [DecidableEq S]

theorem statePairing_smul_left {M : Type*} [Fintype M] (c : ℂ)
    (ψ φ : G → Finset M → ℂ) : statePairing (c • ψ) φ = conj c * statePairing ψ φ := by
  simp only [statePairing, coeffPairing, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun n _ => ?_
  ring

theorem statePairing_smul_right {M : Type*} [Fintype M] (c : ℂ)
    (ψ φ : G → Finset M → ℂ) : statePairing ψ (c • φ) = c * statePairing ψ φ := by
  simp only [statePairing, coeffPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun n _ => ?_
  ring

theorem statePairing_slices {M : Type*} [Fintype M] (χ ξ : G → Finset M → ℂ) :
    statePairing χ ξ = ∑ n, coeffPairing (fun U => χ U n) (fun U => ξ U n) := by
  simp only [statePairing, coeffPairing]
  exact Finset.sum_comm

theorem coeffPairing_mulVec_left' {B : Type*} [Fintype B] (A : Matrix B B ℂ) (x y : B → ℂ) :
    coeffPairing (A *ᵥ x) y = coeffPairing x (Aᴴ *ᵥ y) := by
  rw [Blocks.coeffPairing_eq_dotProduct, Blocks.coeffPairing_eq_dotProduct, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec]

variable [Group G]

theorem tableConv_slice {M : Type*} (k : G → ℂ) (χ : G → Finset M → ℂ) (n : Finset M) :
    (fun V => tableConv k χ V n) = convolution k *ᵥ (fun U => χ U n) := by
  funext V
  rw [Blocks.convolution_mulVec_apply, Blocks.sum_conv_eq_sum_leftWrite, tableConv_apply,
    Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, leftWrite_apply]

/-- A read by a kernel with a self-adjoint convolution matrix is self-adjoint. -/
theorem statePairing_tableConv_adj {M : Type*} [Fintype M] {k : G → ℂ}
    (hk : (convolution k)ᴴ = convolution k) (ψ φ : G → Finset M → ℂ) :
    statePairing (tableConv k ψ) φ = statePairing ψ (tableConv k φ) := by
  rw [statePairing_slices, statePairing_slices]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [tableConv_slice, tableConv_slice, coeffPairing_mulVec_left', hk]

omit [Fintype G] in
/-- The energy kernel is self-adjoint: its levels are real. -/
theorem convolution_energy_conjTranspose [Finite G] {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (E : ι → ℚ) :
    (convolution (responseKernel (fun i => (σ i).character) (fun i => (d i : ℂ))
      fun i => (E i : ℂ)))ᴴ =
      convolution (responseKernel (fun i => (σ i).character) (fun i => (d i : ℂ))
        fun i => (E i : ℂ)) := by
  ext V U
  simp only [Matrix.conjTranspose_apply, convolution, Matrix.of_apply, responseKernel,
    star_mul', star_sum, star_inv₀, Complex.star_def, map_natCast, map_ratCast]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Blocks.character_inv', mul_inv_rev, inv_inv]

omit [Fintype G] [Group G] in
theorem dGamma_conjTranspose {M : Type*} [Fintype M] [DecidableEq M] (ord : LinearOrder M)
    (X : Matrix M M ℂ) : (Fock.dGamma ord X)ᴴ = Fock.dGamma ord Xᴴ := by
  simp only [Fock.dGamma, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, annihilation_conjTranspose, Fock.conjTranspose_creation,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

omit [Fintype G] [Group G] in
theorem hopAt_conjTranspose (ord : LinearOrder (Mode (Fin 3) S)) (U : Matrix (Fin 3) (Fin 3) ℂ) :
    (hopAt ord U)ᴴ = hopAt ord U := by
  rw [hopAt_eq_dGamma, dGamma_conjTranspose, coinK_conjTranspose]

/-- The hop is self-adjoint. -/
theorem statePairing_hop_adj (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (ord : LinearOrder (Mode (Fin 3) S)) (ψ φ : G → Finset (Mode (Fin 3) S) → ℂ) :
    statePairing (hop ρ ord ψ) φ = statePairing ψ (hop ρ ord φ) := by
  simp only [statePairing, hop]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [coeffPairing_mulVec_left', hopAt_conjTranspose]

omit [Fintype G] in
/-- The conjugate of an irreducible triplet is irreducible. -/
theorem conjTripletRep_irreducible {C : Type*} [Fintype C] [DecidableEq C]
    {ρ : G →* Matrix C C ℂ} (h : (tripletRep ρ).IsIrreducible) :
    (conjTripletRep ρ).IsIrreducible := by
  have hconj : ∀ (g : G) (w : C → ℂ),
      (fun c => conj ((tripletRep ρ g w) c)) = conjTripletRep ρ g (fun c => conj (w c)) := by
    intro g w
    funext c
    change conj ((ρ g *ᵥ w) c) = ((ρ g).map (starRingEnd ℂ) *ᵥ fun c => conj (w c)) c
    simp [Matrix.mulVec, dotProduct, map_sum]
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h' => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have h'' := congrArg Subrepresentation.toSubmodule h'
    exact (bot_ne_top : (⊥ : Subrepresentation (tripletRep ρ)) ≠ ⊤)
      (Subrepresentation.toSubmodule_injective h'')
  let W' : Subrepresentation (tripletRep ρ) :=
    ⟨{ carrier := {w | (fun c => conj (w c)) ∈ W.toSubmodule}
       add_mem' := fun {a b} ha hb => by
         simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add] at ha hb ⊢
         exact W.toSubmodule.add_mem ha hb
       zero_mem' := by
         simp only [Set.mem_ofPred_eq, Pi.zero_apply, map_zero]
         exact W.toSubmodule.zero_mem
       smul_mem' := fun c a ha => by
         simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul] at ha ⊢
         exact W.toSubmodule.smul_mem (conj c) ha },
      fun g w hw => by
        change (fun c => conj ((tripletRep ρ g w) c)) ∈ W.toSubmodule
        rw [hconj]
        exact W.apply_mem_toSubmodule g hw⟩
  have hinvol : ∀ v : C → ℂ, (fun c => conj ((fun c => conj (v c)) c)) = v := by
    intro v
    funext c
    exact Complex.conj_conj (v c)
  rcases h.eq_bot_or_eq_top W' with hW | hW
  · left
    apply Subrepresentation.toSubmodule_injective
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    have hmem : (fun c => conj (v c)) ∈ W'.toSubmodule := by
      change (fun c => conj ((fun c => conj (v c)) c)) ∈ W.toSubmodule
      rw [hinvol]
      exact hv
    rw [hW] at hmem
    have h0 : (fun c => conj (v c)) = 0 := (Submodule.mem_bot ℂ).mp hmem
    rw [← hinvol v, h0]
    funext c
    simp
  · right
    apply Subrepresentation.toSubmodule_injective
    refine Submodule.eq_top_iff'.mpr fun v => ?_
    have hmem : (fun c => conj (v c)) ∈ W'.toSubmodule := by
      rw [hW]
      exact Submodule.mem_top
    change (fun c => conj ((fun c => conj (v c)) c)) ∈ W.toSubmodule at hmem
    rwa [hinvol] at hmem

omit [Fintype G] in
/-- An isomorphism carries triviality back. -/
theorem isTrivial_of_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (e : ρ.Equiv τ)
    (h : τ.IsTrivial) : ρ.IsTrivial := by
  refine ⟨fun g => LinearMap.ext fun v => ?_⟩
  apply e.toLinearEquiv.injective
  have := LinearMap.congr_fun (e.isIntertwining' g) v
  simp only [LinearMap.comp_apply] at this
  change e.toLinearMap (ρ g v) = e.toLinearMap v
  rw [this, h.out g]
  rfl

end Energy

section EnergyHop

variable {G : Type*} [Group G] [Fintype G] {S : Type*} [Fintype S] [DecidableEq S]
  {ι : Type*} [Fintype ι] {d : ι → ℕ}

theorem energyKernel_eq_charComb (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)) (E : ι → ℚ) :
    responseKernel (fun i => (σ i).character) (fun i => (d i : ℂ)) (fun i => (E i : ℂ)) =
      Blocks.charComb σ fun i => (E i : ℂ) := by
  funext U
  simp [responseKernel, Blocks.charComb, Nat.card_eq_fintype_card]

/-- The electric energy multiplies the hop of a zero-flux state by the triplet level `E₃`:
every intermediate state has electric energy `E₃`. -/
theorem electricEnergy_hop {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (hirr : (tripletRep ρ).IsIrreducible) (ord : LinearOrder (Mode (Fin 3) S))
    {σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)} (hσ : IsCompleteFamily σ) (E : ι → ℚ)
    (E₃ : ℚ) (hE₃ : ∀ i, (Nonempty ((tripletRep ρ).Equiv (σ i)) ∨
      Nonempty ((conjTripletRep ρ).Equiv (σ i))) → E i = E₃)
    {ψ : G → Finset (Mode (Fin 3) S) → ℂ} (hψ : ψ ∈ zeroFlux ρ ord) :
    electricEnergy σ E (hop ρ ord ψ) = ((E₃ : ℚ) : ℂ) • hop ρ ord ψ := by
  obtain ⟨i3, ⟨e3⟩⟩ := hσ.2.2 3 (tripletRep ρ) hirr
  obtain ⟨i3b, ⟨e3b⟩⟩ := hσ.2.2 3 (conjTripletRep ρ) (conjTripletRep_irreducible hirr)
  have hE3 : E i3 = E₃ := hE₃ i3 (Or.inl ⟨e3⟩)
  have hE3b : E i3b = E₃ := hE₃ i3b (Or.inr ⟨e3b⟩)
  funext V n
  have hslice := congrFun (tableConv_slice (responseKernel (fun i => (σ i).character)
    (fun i => (d i : ℂ)) fun i => (E i : ℂ)) (hop ρ ord ψ) n) V
  rw [electricEnergy, hslice, energyKernel_eq_charComb]
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hop_mem_blocks ord ρ hψ n)
  rw [← block_eq_of_equiv e3] at hy
  rw [← block_eq_of_equiv e3b] at hz
  rw [← hyz, Matrix.mulVec_add, Blocks.convolution_charComb σ hσ.1 hσ.2.1 _ i3 hy,
    Blocks.convolution_charComb σ hσ.1 hσ.2.1 _ i3b hz, hE3, hE3b, ← smul_add, hyz]
  rfl

omit [Fintype G] in
/-- An irreducible triplet is not trivial. -/
theorem not_isTrivial_tripletRep {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}
    (hirr : (tripletRep ρ).IsIrreducible) : ¬ (tripletRep ρ).IsTrivial := by
  intro h
  have h0 := Moments.eq_zero_of_invariant hirr (v := Pi.single 0 1) fun g => by
    have := LinearMap.congr_fun (h.out g) (Pi.single 0 1)
    exact this
  have := congrFun h0 0
  simp at this

end EnergyHop

end ThereAndBack

namespace ThereAndBack

open Edge

section Projector

variable {G : Type*} [Group G] [Fintype G] {C S : Type*} [Fintype C] [DecidableEq C]
  [Fintype S] [DecidableEq S]

/-- The average of the gauge pairs, `Π = (1/|G|²) Σ_h Γ(D(h))`. -/
noncomputable def pairAvg (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ :=
  (Fintype.card (G × G) : ℂ)⁻¹ • ∑ h, pairHom ρ ord h

/-- The orthogonal projector onto the zero-flux sector: average over the link, then over the
gauge pairs, `ψ ↦ (U ↦ Π ((1/|G|) Σ_V ψ(V)))`. -/
noncomputable def zeroFluxProj (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) :
    (G → Finset (Mode C S) → ℂ) →ₗ[ℂ] (G → Finset (Mode C S) → ℂ) where
  toFun ψ := fun _ => pairAvg ρ ord *ᵥ ((Fintype.card G : ℂ)⁻¹ • ∑ V, ψ V)
  map_add' ψ φ := by
    funext U
    simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add, Matrix.mulVec_add]
  map_smul' c ψ := by
    funext U
    simp only [Pi.smul_apply, RingHom.id_apply, ← Finset.smul_sum, smul_comm c,
      Matrix.mulVec_smul]

theorem pairHom_mul_pairAvg (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) (g : G × G) :
    pairHom ρ ord g * pairAvg ρ ord = pairAvg ρ ord := by
  rw [pairAvg, Matrix.mul_smul, Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => (map_mul _ g h).symm

theorem pairAvg_conjTranspose {ρ : G →* Matrix C C ℂ} (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ)
    (ord : LinearOrder (Mode C S)) : (pairAvg ρ ord)ᴴ = pairAvg ρ ord := by
  have hunit : ∀ h : G × G, pairHom ρ ord h ∈ Matrix.unitaryGroup _ ℂ := fun h =>
    Fock.secondQuant_mem_unitaryGroup ord (diag_mem_unitaryGroup (hρ h.1) (hρ h.2))
  have hinv : ∀ h : G × G, (pairHom ρ ord h)ᴴ = pairHom ρ ord h⁻¹ := by
    intro h
    rw [← Fock.inv_eq_conjTranspose_of_mem (hunit h)]
    refine Matrix.inv_eq_left_inv ?_
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [pairAvg, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum, star_inv₀, Complex.star_def,
    map_natCast]
  congr 1
  simp only [hinv]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ fun h => rfl

theorem zeroFluxProj_mem (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (ψ : G → Finset (Mode C S) → ℂ) : zeroFluxProj ρ ord ψ ∈ zeroFlux ρ ord := by
  rw [mem_zeroFlux_iff]
  refine ⟨fun U => rfl, fun h => ?_⟩
  change pairHom ρ ord h *ᵥ (pairAvg ρ ord *ᵥ _) = pairAvg ρ ord *ᵥ _
  rw [Matrix.mulVec_mulVec, pairHom_mul_pairAvg]

theorem zeroFluxProj_fix (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    {ψ : G → Finset (Mode C S) → ℂ} (hψ : ψ ∈ zeroFlux ρ ord) : zeroFluxProj ρ ord ψ = ψ := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc2 : (Fintype.card (G × G) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mem_zeroFlux_iff] at hψ
  funext U
  change pairAvg ρ ord *ᵥ ((Fintype.card G : ℂ)⁻¹ • ∑ V, ψ V) = ψ U
  simp only [hψ.1, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hc, one_smul]
  rw [pairAvg, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [hψ.2, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hc2, one_smul]

theorem zeroFluxProj_adj {ρ : G →* Matrix C C ℂ} (hρ : ∀ g, ρ g ∈ Matrix.unitaryGroup C ℂ)
    (ord : LinearOrder (Mode C S)) (ψ φ : G → Finset (Mode C S) → ℂ) :
    statePairing (zeroFluxProj ρ ord ψ) φ = statePairing ψ (zeroFluxProj ρ ord φ) := by
  change ∑ U, coeffPairing (pairAvg ρ ord *ᵥ ((Fintype.card G : ℂ)⁻¹ • ∑ V, ψ V)) (φ U) =
    ∑ U, coeffPairing (ψ U) (pairAvg ρ ord *ᵥ ((Fintype.card G : ℂ)⁻¹ • ∑ V, φ V))
  have hleft : ∀ y : Finset (Mode C S) → ℂ, ∑ U, coeffPairing (ψ U) y =
      coeffPairing (∑ V, ψ V) y := by
    intro y
    simp only [coeffPairing, Finset.sum_apply, map_sum, Finset.sum_mul]
    exact Finset.sum_comm
  rw [← Fock.coeffPairing_sum_right, ThereAndBack.coeffPairing_mulVec_left',
    pairAvg_conjTranspose hρ, hleft, Matrix.mulVec_smul, Blocks.coeffPairing_smul_left,
    Blocks.coeffPairing_smul_right, map_inv₀, map_natCast]

end Projector

end ThereAndBack

open Edge ThereAndBack NormedSpace in
/-- **Theorem 11.20** (the there-and-back tally). Let `P` be the projector onto the zero-flux
sector, and `A_{cc'} = Σ_s a†_{ycs} a_{xc's}`. Then `P V P = 0`, the hop moves the link's table
into the triplet block or its conjugate, and `P V² P = Ω`, with `m = 1` for a real triplet and
`m = 0` when `3 ⊗ 3` has no invariant, both sides restricted to the sector. Consequently the
family of coins `Γ(e^{iθ K_U}) = e^{iθ V_U}`, of which the native coin is the member `θ = π/4`,
returns to the sector as `P 𝒞_θ P = P - (θ²/2) Ω + O(θ³)`, and the second-order shift of the
energy law on the sector is `-Ω/(κ E₃)`. -/
@[book "thm:mt-there-and-back"]
theorem mtThereAndBack : Statement.mtThereAndBack := by
  intro G _ _ S _ _ ρ hρ hirr ord ι _ d σ hσ E hE E₃ hE₃ κ hκ m hm P hP1 hP2 hP3
  classical
  have hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ := fun g =>
    (Matrix.mem_specialUnitaryGroup_iff.mp (hρ g)).1
  have hmom := mtMoments G ρ hρ hirr
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : ∑ U, ρ U = 0 := by
    have := hmom.1
    rwa [smul_eq_zero, or_iff_right (inv_ne_zero hcard)] at this
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
  -- the tally keeps the zero-flux sector
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
  -- pairing a sector state with `V²`
  have hpairV2 : ∀ ξ ∈ zeroFlux ρ ord, ∀ ψ ∈ zeroFlux ρ ord,
      statePairing ξ (hop ρ ord (hop ρ ord ψ)) = statePairing ξ (atEachLink (tally ord m) ψ) := by
    intro ξ hξ ψ hψ
    rw [const_of_mem_zeroFlux hξ, const_of_mem_zeroFlux hψ]
    have e1 : hop ρ ord (hop ρ ord (fun _ => ψ 1)) =
        fun U => (hopAt ord (ρ U) * hopAt ord (ρ U)) *ᵥ ψ 1 := by
      funext U
      simp only [hop, Matrix.mulVec_mulVec]
    have e2 : atEachLink (tally ord m) (fun _ : G => ψ 1) = fun _ : G => tally ord m *ᵥ ψ 1 := rfl
    rw [e1, e2, statePairing_const_atEach, statePairing_const_atEach, hsq, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  have hPV : ∀ ψ, P (hop ρ ord (P ψ)) = 0 := fun ψ =>
    proj_eq_zero_of_orth hP1 hP2 hP3 fun ξ hξ => statePairing_hop_eq_zero ord h1 hξ (hP1 ψ)
  have hPVV : ∀ ψ ∈ zeroFlux ρ ord,
      P (hop ρ ord (hop ρ ord ψ)) = atEachLink (tally ord m) ψ :=
    fun ψ hψ => proj_eq_of_orth hP1 hP2 hP3 (hΩmem ψ hψ) fun ξ hξ => hpairV2 ξ hξ ψ hψ
  refine ⟨hPV, fun ψ hψ n => hop_mem_blocks ord ρ hψ n, hPVV,
    fun θ U => secondQuant_exp_coinK ord (hunit U) _, fun U => exp_pi_div_four_coinK (hunit U),
    ?_, ?_⟩
  · -- the return of the family of coins, to order `θ³`
    set cP : ℝ := ‖LinearMap.toContinuousLinearMap P‖
    have hcP : ∀ x, ‖P x‖ ≤ cP * ‖x‖ := fun x => (LinearMap.toContinuousLinearMap P).le_opNorm x
    have hcP0 : 0 ≤ cP := norm_nonneg _
    set B : G → ℝ := fun U => ∑ i, ∑ j, ∑ k, ‖Fock.secondQuant ord (Qm (ρ U)) i k‖ *
      ‖(Fock.secondQuant ord (Qm (ρ U)))⁻¹ k j‖ * (4 * ‖occSum k‖ ^ 3)
    have hB0 : ∀ U, 0 ≤ B U := fun U => by positivity
    set N : ℕ := Fintype.card (Finset (Mode (Fin 3) S))
    refine ⟨cP * (N * ∑ U, B U), fun θ ψ hψ => ?_⟩
    set R : G → Matrix (Finset (Mode (Fin 3) S)) (Finset (Mode (Fin 3) S)) ℂ := fun U =>
      exp (((θ : ℂ) * Complex.I) • hopAt ord (ρ U)) - 1 -
        ((θ : ℂ) * Complex.I) • hopAt ord (ρ U) -
          (((θ : ℂ) * Complex.I) ^ 2 / 2) • (hopAt ord (ρ U) * hopAt ord (ρ U))
    set Rψ : G → Finset (Mode (Fin 3) S) → ℂ := fun U => R U *ᵥ ψ U
    have hcoin : coinFamily ρ ord θ ψ = ψ + ((θ : ℂ) * Complex.I) • hop ρ ord ψ +
        (((θ : ℂ) * Complex.I) ^ 2 / 2) • hop ρ ord (hop ρ ord ψ) + Rψ := by
      funext U
      simp only [coinFamily, secondQuant_exp_coinK ord (hunit U), Rψ, R, hop, Pi.add_apply,
        Pi.smul_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_mulVec]
      abel
    have hdiff : P (coinFamily ρ ord θ ψ) - (ψ - ((θ : ℂ) ^ 2 / 2) • atEachLink (tally ord m) ψ) =
        P Rψ := by
      have hPVψ : P (hop ρ ord ψ) = 0 := by
        have := hPV ψ
        rwa [hP2 ψ hψ] at this
      rw [hcoin, map_add, map_add, map_add, map_smul, map_smul, hP2 ψ hψ, hPVV ψ hψ, hPVψ,
        smul_zero, add_zero,
        show ((θ : ℂ) * Complex.I) ^ 2 / 2 = -((θ : ℂ) ^ 2 / 2) by rw [mul_pow, Complex.I_sq]; ring,
        neg_smul]
      abel
    rw [hdiff]
    have hR : ‖Rψ‖ ≤ ((N : ℝ) * ∑ U, B U) * |θ| ^ 3 * ‖ψ‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun U => ?_
      calc ‖Rψ U‖ = ‖R U *ᵥ ψ U‖ := rfl
        _ ≤ ((N : ℝ) * (B U * |θ| ^ 3)) * ‖ψ U‖ :=
          norm_mulVec_le (R U) (by positivity)
            (fun i j => norm_remainder_apply_le ord (hunit U) θ i j) (ψ U)
        _ ≤ ((N : ℝ) * ((∑ U, B U) * |θ| ^ 3)) * ‖ψ‖ := by
          gcongr
          · exact Finset.single_le_sum (fun U _ => hB0 U) (Finset.mem_univ U)
          · exact norm_le_pi_norm ψ U
        _ = ((N : ℝ) * ∑ U, B U) * |θ| ^ 3 * ‖ψ‖ := by ring
    calc ‖P Rψ‖ ≤ cP * ‖Rψ‖ := hcP Rψ
      _ ≤ cP * (((N : ℝ) * ∑ U, B U) * |θ| ^ 3 * ‖ψ‖) := by gcongr
      _ = cP * ((N : ℝ) * ∑ U, B U) * |θ| ^ 3 * ‖ψ‖ := by ring
  · -- the second-order shift of the energy law
    intro ψ hψ
    have hPψ : P ψ = ψ := hP2 ψ hψ
    have hPVψ : P (hop ρ ord ψ) = 0 := by
      have := hPV ψ
      rwa [hPψ] at this
    obtain ⟨i3, ⟨e3⟩⟩ := hσ.2.2 3 (tripletRep ρ) hirr
    have hE3pos : (0 : ℚ) < E₃ := by
      rw [← hE₃ i3 (Or.inl ⟨e3⟩)]
      exact (hE i3).2 fun htriv => not_isTrivial_tripletRep hirr (isTrivial_of_equiv e3 htriv)
    have hE3 : ((E₃ : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hE3pos.ne'
    have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hEV : ∀ ξ ∈ zeroFlux ρ ord,
        electricEnergy σ E (hop ρ ord ξ) = ((E₃ : ℚ) : ℂ) • hop ρ ord ξ :=
      fun ξ hξ => electricEnergy_hop hirr ord hσ E E₃ hE₃ hξ
    have hcκ : (((κ * E₃ : ℝ)) : ℂ) = (κ : ℂ) * ((E₃ : ℚ) : ℂ) := by push_cast; ring
    rw [hPψ, hPVψ, sub_zero]
    refine ⟨⟨(((κ * E₃ : ℝ)) : ℂ)⁻¹ • hop ρ ord ψ, ?_, ?_⟩, fun χ hχ1 hχ2 => ?_⟩
    · rw [map_smul, hPVψ, smul_zero, sub_zero]
    · rw [electricEnergy, tableConv_smul, ← electricEnergy, hEV ψ hψ, smul_smul, smul_smul, hcκ]
      rw [show (κ : ℂ) * ((κ : ℂ) * ((E₃ : ℚ) : ℂ))⁻¹ * ((E₃ : ℚ) : ℂ) = 1 by
        field_simp, one_smul]
    · rw [hχ1]
      have hHχ : electricEnergy σ E χ = (κ : ℂ)⁻¹ • hop ρ ord ψ := by
        rw [← hχ2, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
      congr 1
      refine proj_eq_of_orth hP1 hP2 hP3 ((zeroFlux ρ ord).smul_mem _ (hΩmem ψ hψ))
        fun ξ hξ => ?_
      have hVξ : hop ρ ord ξ = ((E₃ : ℚ) : ℂ)⁻¹ • electricEnergy σ E (hop ρ ord ξ) := by
        rw [hEV ξ hξ, smul_smul, inv_mul_cancel₀ hE3, one_smul]
      have step1 : statePairing ξ (hop ρ ord χ) = statePairing (hop ρ ord ξ) χ :=
        (statePairing_hop_adj ρ ord ξ χ).symm
      have step2 : statePairing (hop ρ ord ξ) χ =
          ((E₃ : ℚ) : ℂ)⁻¹ * statePairing (hop ρ ord ξ) (electricEnergy σ E χ) := by
        conv_lhs => rw [hVξ]
        rw [statePairing_smul_left]
        congr 1
        · simp [map_inv₀, map_ratCast]
        · exact statePairing_tableConv_adj (convolution_energy_conjTranspose σ E) _ _
      have step3 : statePairing ξ ((((κ * E₃ : ℝ)) : ℂ)⁻¹ • atEachLink (tally ord m) ψ) =
          (((κ * E₃ : ℝ)) : ℂ)⁻¹ * statePairing (hop ρ ord ξ) (hop ρ ord ψ) := by
        rw [statePairing_smul_right, ← hpairV2 ξ hξ ψ hψ, ← statePairing_hop_adj]
      rw [step1, step2, hHχ, statePairing_smul_right, step3, hcκ]
      field_simp

/-! ## Non-vacuity -/

section NonVacuity

open Edge ThereAndBack

theorem cubeTriplet_real (U : cubeGroup) (i j : Fin 3) :
    conj (cubeTriplet U i j) = cubeTriplet U i j := by
  obtain ⟨p, rfl⟩ := CubeGroup.exists_toGroup U
  simp only [cubeTriplet, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    Submonoid.coe_subtype, CubeGroup.toGroup_val, signedPermMatrix, Matrix.of_apply]
  split_ifs <;> simp

/-- Theorem 11.20 on the book's running example, one edge with one slot over the cube group. Its
hypotheses are met: the triplet is irreducible and real (`m = 1`), a complete family of
irreducible representations exists, the levels `E = 4/3` on the nontrivial blocks and `0` on the
trivial one form an energy table with `E₃ = 4/3`, `κ = 1`, and `zeroFluxProj` is an orthogonal
projector onto the zero-flux sector. Hence `P V P = 0` there. -/
example : letI := CubeGroup.fintype
    ∀ ψ, zeroFluxProj cubeTriplet oneSlotOrder
      (hop cubeTriplet oneSlotOrder (zeroFluxProj cubeTriplet oneSlotOrder ψ)) = 0 := by
  let := CubeGroup.fintype
  classical
  obtain ⟨n, d, σ, h1, h2, h3⟩ := (mtBlocks cubeGroup).1
  have hσ : IsCompleteFamily σ := ⟨h1, h2, h3⟩
  let E : Fin n → ℚ := fun i => if (σ i).IsTrivial then 0 else 4 / 3
  have hE : IsEnergyTable σ E := fun i =>
    ⟨fun h => by simp [E, h], fun h => by simp only [E, h, ite_false]; norm_num⟩
  have hirr := CubeGroup.isIrreducible_tripletRep
  have hE3 : ∀ i, (Nonempty ((tripletRep cubeTriplet).Equiv (σ i)) ∨
      Nonempty ((conjTripletRep cubeTriplet).Equiv (σ i))) → E i = 4 / 3 := by
    rintro i (⟨⟨e⟩⟩ | ⟨⟨e⟩⟩)
    · have : ¬ (σ i).IsTrivial := fun h =>
        not_isTrivial_tripletRep hirr (isTrivial_of_equiv e h)
      simp [E, this]
    · have : ¬ (σ i).IsTrivial := fun h =>
        not_isTrivial_tripletRep (ρ := (RingHom.mapMatrix (starRingEnd ℂ)).toMonoidHom.comp
          cubeTriplet) (conjTripletRep_irreducible hirr) (isTrivial_of_equiv e h)
      simp [E, this]
  exact (mtThereAndBack cubeGroup (Fin 1) cubeTriplet cubeTriplet_mem hirr oneSlotOrder
    (Fin n) d σ hσ E hE (4 / 3) hE3 1 one_pos 1 (Or.inl ⟨rfl, cubeTriplet_real⟩)
    (zeroFluxProj cubeTriplet oneSlotOrder) (zeroFluxProj_mem _ _)
    (fun _ hψ => zeroFluxProj_fix _ _ hψ) (zeroFluxProj_adj cubeTriplet_unitary _)).1

end NonVacuity

end Artform
